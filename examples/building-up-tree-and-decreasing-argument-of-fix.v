(*|
###############################################
Building up tree and decreasing argument of fix
###############################################

:Link: https://stackoverflow.com/questions/56132183/building-up-tree-and-decreasing-argument-of-fix
|*)

(*|
Question
********

I'm attempting to implement a function to build up a Braun tree with n
elements using the following function in Coq, but Coq gives me the
error that it cannot guess decreasing argument of fix:
|*)

Require Import Coq.Init.Nat.

Parameter V : Type.

Inductive BraunTree : Type :=
| E : BraunTree
| T : V -> BraunTree -> BraunTree -> BraunTree.

Fail Fixpoint copy (x : V) (n : nat) : BraunTree :=
  let
    fix copy2 (a : V) (i : nat) : (BraunTree * BraunTree) :=
    match i with
    | 0 => (T a E E, E)
    | _ => match Nat.odd i with
           | true => let m := (i - 1) / 2 in
                     let (s,t) := copy2 a m in
                     (T a s t, T a t t)
           | false => let m := (i - 2) / 2 in
                      let (s, t) := copy2 a m in
                      (T a s s, T a s t)
           end
    end
  in
  match copy2 x n with
  | (_, snd) => snd
  end. (* .fails *)

(*|
I know that it is not the separate even and odd cases that is the
problem because it gave the same error when I removed the even/odd
cases:
|*)

Fail Fixpoint copy (x : V) (n : nat) : BraunTree :=
  let
    fix copy2 (a : V) (i : nat) : (BraunTree * BraunTree) :=
    match i with
    | 0 => (T a E E, E)
    | _ => let m := (i - 1) / 2 in
           let (s, t) := copy2 a m in
           (T a s t, T a t t)
    end
  in
  match copy2 x n with
  | (_, snd) => snd
  end. (* .fails *)

(*| How can I convince Coq that i is in fact a decreasing argument? |*)

(*|
Answer
******

``Fixpoint``/``fix`` only allows recursive calls on a *syntactically*
smaller argument.

.. code-block:: coq

    Fixpoint example (n : nat) :=
      ... (* There must be a match on [n] somewhere *)
        ... match n with
            | O => base_case (* no recursive call allowed *)
            | S m =>
              ... (example m)
              (* We can only call [example] on [m], or some even
                 smaller value obtained by matching on [m] *)
            end ...

In particular, it's not allowed to make a recursive call on a value
obtained via some arbitrary function (in this case, ``div`` and
``sub`` in ``copy2 a ((i - 1) / 2)``).

Here are three options:

1. Pick another representation of natural numbers so that
   pattern-matching on it naturally decomposes into the different
   branches of the desired definition (base case (zero), even, odd).
2. Use the fact that the recursion depth is actually bounded by ``n``,
   so we can use ``n`` as "fuel", which we know will not actually
   deplete before we are done.
3. Cunningly extract a subterm of the decreasing argument to make the
   recursive call. This solution is less general and robust than the
   previous ones; it's a much harder fight against the termination
   checker.

----

Alternative representation
==========================

We have three cases: zero, even, and odd. Luckily the standard library
has a type with almost the same structure, ``positive``:
|*)

Inductive positive :=    (* p > 0 *)
| xH                     (* 1 *)
| xI (p : positive)      (* 2p + 1 *)
| xO (p : positive).     (* 2p     *)

(*|
Pointing the type ``positive`` with an additional zero, we get ``N``:
|*)

Inductive N :=
| N0                      (* 0 *)
| Npos (p : positive).    (* p > 0 *)

(*|
There is also a conversion function ``N.of_nat : nat -> N``, although
it might also be a good idea to use ``N`` everywhere instead of
``nat``, if the conversions become too annoying.

The final definition starts by case analysis on ``N``, and the case
revealing a ``positive`` number is handled with a ``fix``-point, where
the base case is ``1`` instead of ``0``. We have to shift some
details, because the even case is ``2p`` instead of ``2p + 2``, so
instead of a pair of trees of size ``(i+1, i)`` we have to do ``(i-1,
i)``. But overall the recursive cases still naturally match an
informal specification:
|*)

Reset V. (* .none *)
Require Import NArith PArith.

Parameter V : Type.

Inductive BraunTree : Type :=
| E : BraunTree
| T : V -> BraunTree -> BraunTree -> BraunTree.

Definition copy (x : V) (n : N) : BraunTree :=
  match n with
  | N0 => E
  | Npos p =>
    let
      (* copy2 a i : a tree of (i-1) copies of a, and another of i
         copies of a *)
      fix copy2 (a : V) (i : positive) : (BraunTree * BraunTree) :=
      match i with
      | xH => (* i = 1 *)
        (E, T a E E)
      | xI p => (* i = 2p + 1 *)
        let (s, t) := copy2 a p in
        (T a t s, T a t t)
      | xO p => (* i = 2p *)
        let (s, t) := copy2 a p in
          (T a s s, T a t s)
      end
    in
    match copy2 x p with
    | (_, snd) => snd
    end
  end.
Reset copy. (* .none *)

(*|
----

Just enough fuel
================

We add fuel to the ``fix`` as the decreasing argument. We can only run
out if ``n = i = 0``, so we know what the result should be then.
|*)

(* note: This doesn't need to be a Fixpoint *)
Definition copy (x : V) (n : nat) : BraunTree :=
  let
    fix copy2 (a : V) (n : nat) (i : nat) : (BraunTree * BraunTree) :=
    match n with
    | O => (T a E E, E)
    | S n' =>
      match i with
      | O => (T a E E, E)
      | _ =>
        if Nat.odd i then
          let m := div2 ((i - 1) / 2) in
          let (s, t) := copy2 a n' m in
          (T a s t, T a t t)
        else
          let m := div2 ((i - 2) / 2) in
          let (s, t) := copy2 a n' m in
          (T a s s, T a s t)
      end
    end
  in
  match copy2 x n n with
  | (_, snd) => snd
  end.
Reset copy. (* .none *)

(*|
This works nicely when:

- we can compute the amount of fuel needed;
- and there is a predictable answer to give when we run out of fuel.

If either of those assumption does *not* hold, we need to litter our
code with ``option``.

----

Nested recursion
================

As mentioned earlier, Coq has strict rules about decreasing arguments.
The usual explanation is that we can only make a recursive call on a
subterm obtained through pattern-matching on the decreasing argument
(or transitively, one of its subterms).

One apparent restriction is that, because the condition is syntactic
(i.e., Coq looks at the definition to track the provenance of the
decreasing argument), the argument ``n`` can only decrease by a
constant at most (constant with respect to ``n``), since there are
only finitely many ``match`` in a definition. In particular, there is
no way to make a recursive call on the result of a division by two, as
that represents a decrease by ``n/2``, a value linear in ``n``.

For better or for worse, Coq's termination criterion is actually a bit
smarter than that: one can pass the decreasing argument to a nested
fixpoint, and the "subterm" relation will be tracked through it.

Cons-free division
------------------

And indeed, the division of a Peano ``nat`` can be defined in such a
way that Coq can tell that the result is a subterm of the dividend:
|*)

Definition div2 (n : nat) :=
  let fix d2 (n1 : nat) (n2 : nat) {struct n1} :=
      match n2 with
      | S (S n2') =>
        match n1 with
        | O => n1
        | S n1' => d2 n1' n2'
        end
      | _ => n1
      end
  in d2 n n.

(*|
The idea is to write a ``fix``-point of two arguments (somewhat like
the fuel solution), which start out equal (``d2 n n``), and we remove
**two** ``S`` constructors from one (``n2``) of them for every **one**
``S`` we remove from the other (``n1``). Important details:

- In all the non-recursing cases, we return ``n1`` (and *not* ``0`` in
  any case), which is then guaranteed to be a subterm of the topmost
  ``n``.
- And the function must be decreasing in ``n1`` (the term we return),
  rather than ``n2`` (Coq only keeps track of subterms of decreasing
  arguments).

All that ensures that ``div2 n`` is a subterm of ``n`` (not a *strict
subterm* (or *proper subterm*\ ), because ``n`` could be ``O``).

This has similarities to the previous fuel-based solution, but here
the decreasing argument is a lot more relevant than just a device to
trick the type checker.

This technique is a variant of *cons-free programming*. (Note though
that the constraints are not quite the same as what is discussed in
the literature, for example when the focus is on avoiding *memory
allocations* rather than ensuring *termination* by structural
well-foundedness.)

Conclusion: definition of ``copy``
----------------------------------

Once we have ``div2``, we can define ``copy`` with a few tweaks to
obtain ``i-1`` and ``i-2`` as *proper subterms* of ``i``, again by
pattern-matching. Below, ``i'`` and ``i''`` are proper subterms of
``i`` (by visual inspection), and ``div2 i'`` and ``div2 i''`` are
subterms of ``i'`` and ``i''`` (by the definition of ``div2``). By
transitivity they are proper subterms of ``i``, so the termination
checker accepts.
|*)

Definition copy (x : V) (n : nat) : BraunTree :=
  let
    fix copy2 (a : V) (i : nat) : (BraunTree * BraunTree) :=
    match i with
    | 0 => (T a E E, E)
    | S i' => (* i' = i-1 *)
      if Nat.odd i then
        let m := div2 i' in
        let (s, t) := copy2 a m in
        (T a s t, T a t t)
      else
        match i' with
        | O => (* Unreachable *) (E, E)
        | S i'' => (* i'' = i-2 *)
          let m := div2 i'' in
          let (s, t) := copy2 a m in
          (T a s s, T a s t)
        end
    end
  in
  match copy2 x n with
  | (_, snd) => snd
  end.
