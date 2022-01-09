(*|
####################################################################
How to make use of information known about this function type in Coq
####################################################################

:Link: https://stackoverflow.com/q/48959586
|*)

(*|
Question
********

Say I have the following type ``typ`` representing ``bool`` or
``nat``:
|*)

Inductive typ : Type := TB | TN.

(*|
I also have a function to extract an actual function type from a list
of ``typ``\ s and a result type:
|*)

From Coq Require Import ssreflect. (* .none *)
From mathcomp Require Import seq. (* .none *)
Fixpoint get_types (s: seq typ) (result_type: Type) : Type :=
  match s with
  | nil => result_type
  | x :: xs => match x with
               | TN => nat -> get_types xs result_type
               | TB => bool -> get_types xs result_type
               end
  end.

Example get_types_works : get_types (TB :: TN :: nil) nat = bool -> nat -> nat.
Proof. by []. Qed.

(*|
Now, I have another function that takes as input a list ``s`` of
``typ``\ s and a function of type ``get_types s``:
|*)

Fail Fixpoint app (s: seq typ) (constructor: get_types s nat) : nat :=
  match s with
  | nil => 2 (* Not properly handling empty list case for now *)
  | TB :: nil => constructor true
  | TN :: nil => constructor 2
  | TB :: xs => app xs (constructor true)
  | TN :: xs => app xs (constructor 2)
  end. (* .fails .unfold *)

(*|
Defining the above function fails at the line ``| TB :: nil =>
constructor true``.

Given we know here that the type of ``get_types s nat`` should be
``bool -> nat``, as the value of ``s`` is ``TB :: nil``, I'm wondering
if there's a way we can make Coq aware of this so that the above
function can be defined?

If not, is this a limitation of Coq or would the same apply to other
dependently typed languages?

**Edit:** For context, this is not the original problem I'm trying to
solve; it's a condensed version to show the issue I was having with
the type system. In the actual version, rather than hard-coding ``2``
and ``true``, the ``typ``-like datastructure also carries indices of
data to parse from a memory slice, and validation functions. The aim
for ``app`` is a function that takes a list of such ``typ``\ s, a
slice, and a constructor for a record containing such types, then
constructs an instance of that record from the indices of the types to
parse, or returns ``None`` if any of the validations fail.
|*)

(*|
Answer (Tej Chajed)
*******************

There's nothing wrong with what you want in principle. However, at
least in Coq, there are some simple rules for how pattern matching is
typechecked so that information about which constructor was used can
be used in the type. The surface language (Gallina in this case) hides
this simplicity by helping compile (or *desugar*\ ) pattern matches,
so that as a user you can write more complex patterns than the
underlying system has to deal with. I'm not as familiar with Idris,
but based on how complicated dependent pattern matches can be I
suspect you run into similar limitations there, where you have to fit
your code into a form the system can type check.

Here, you're running into two limitations of this pattern matching
compilation. The first is that the type of constructor is not
specialized based on the match on ``s``. This is easily fixed by
computing a function from ``get_types s nat -> nat``, which the
compiler gets right.
|*)

Reset Initial. (* .none *)
Require Import List.
Import ListNotations.

Inductive typ : Type := TB | TN.

Fixpoint get_types (s: list typ) (result_type: Type) : Type :=
  match s with
  | nil => result_type
  | x :: xs => match x with
               | TN => nat -> get_types xs result_type
               | TB => bool -> get_types xs result_type
               end
  end.

Fail Fixpoint app (s: list typ) : get_types s nat -> nat :=
  match s with
  | nil => fun constructor => 2
  | TB :: nil => fun constructor => constructor true
  | TN :: nil => fun constructor => constructor 2
  | TB :: xs => fun constructor => app xs (constructor true)
  | TN :: xs => fun constructor => app xs (constructor 2)
  end. (* .fails *)
(* fails due to limitation of termination checker with nested matches *)

(*|
...but then you run into a second problem with the termination
checker. Note that your match is complex: it analyzes the structure of
``s`` as well as its head and tail (if it was built with ``cons``).
Ultimately all pattern matches are compiled to nested pattern matches
on a single inductive type. If you look at this unfolding, you're
destructing ``s`` into ``t :: xs``, and then destructing ``xs`` again
into ``t0 :: xs'``, before finally recursing on ``xs``. Unfortunately,
the Coq termination checker only sees this as ``t0 :: xs'`` and
doesn't recognize it as a subterm of ``s`` (it really wants ``xs``).

I had a hard time manually writing your function in a way that type
checks, but here's a version written using tactics that is
functionally correct. Note that the definition it produces is quite a
bit more complicated than any ordinary pattern match, because it has
to maintain a proof produced by ``destruct_with_eqn``. However, that
proof is crucial to simultaneously using ``xs`` to make the
termination checker happy and revealing ``t0 :: xs'`` for type
checking the application of the constructor. It may be complicated but
you can still run it just fine, as the last line illustrates.
|*)

Fixpoint app (s: list typ) (constructor: get_types s nat) {struct s} : nat.
  destruct s as [|t xs]; simpl in *.
  - exact 2.
  - destruct_with_eqn xs; simpl in *.
    + destruct t; [ exact (constructor true) | exact (constructor 2) ].
    + destruct t; simpl in *.
      * apply (app xs). subst. exact (constructor true).
      * apply (app xs). subst. exact (constructor 2).
Defined.

Eval compute in app [TB; TN] (fun x y => if x then y + 2 else y). (* .unfold *)

(*|
Answer (eponier)
****************

Yet two other ways of defining ``app``.

The first one uses tactics, and relies on ``induction`` instead of
``Fixpoint``.
|*)

Reset app. (* .none *)
From mathcomp Require Import seq. (* .none *)
Definition app (s: seq typ) (constructor: get_types s nat) : nat.
Proof.
  induction s as [|t xs].
  - exact 2.
  - destruct xs.
    + destruct t.
      * exact (constructor true).
      * exact (constructor 2).
    + destruct t.
      * exact (IHxs (constructor true)).
      * exact (IHxs (constructor 2)).
Defined.

(*| The second one uses Gallina and complexed pattern-matchings. |*)

Reset app. (* .none *)
Fixpoint app (s: seq typ) : get_types s nat -> nat :=
  match s return get_types s nat -> nat with
  | nil => fun _ => 2
  | x :: xs =>
    match xs as xs0 return xs = xs0 -> get_types (x::xs0) nat -> nat with
    | nil => fun _ => match x return get_types (x::nil) nat -> nat with
                      | TB => fun c => c true
                      | TN => fun c => c 2
                      end
    | _ => fun e => match e in _ = xs1 return get_types (x::xs1) nat -> nat with
                    | eq_refl =>
                      match x return get_types (x::xs) nat -> nat with
                      | TB => fun c => app xs (c true)
                      | TN => fun c => app xs (c 2)
                      end
                    end
    end eq_refl
  end.

(*|
When destructing ``xs``, we remember an equality between the original
``xs`` and what it is destructed in. We do not need this equality in
the ``nil`` branch and discards it with ``fun _``. In the other
branch, we pattern-match on the proof of equality (``match e``), which
corresponds to a rewriting using this equality. Inside the ``eq_refl``
branch, we can use the original ``xs`` and thus make recursive calls
allowed by the termination checker. Outside the pattern-match, we
return the right type expected by the pattern-matching on ``xs``. The
last thing to do is to provide a proof of the equality of ``xs`` and
``xs0``, but it is trivially ``eq_refl``.
|*)

(*|
Answer (ejgallego)
******************

Well, I am not sure what you are really trying to do, but the first
step to submit your code into the "convoy" pattern is indeed to add a
bit more structure to you type interpretation. If you separate the
interpretation of types from the one for list of types you can easily
get a skeleton working:
|*)

Reset Initial. (* .none *)
Set Warnings "-notation-overridden". (* .none *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Typ := TB | TN.

(* Interpretation for types *)
Definition iT w : Type :=
  match w with | TB => bool | TN => nat end.

(* Default witness *)
Definition dw w : iT w :=
  match w with | TB => true | TN => 2 end.

Definition get_types (res : Type) :=
  fix gt (args : list Typ) :=
    match args with
    | [::]        => res
    | [:: w & xs] => iT w -> gt xs
    end.

Variable (dt : Typ).
Fixpoint app (args : list Typ) : get_types (iT dt) args -> iT dt :=
  match args with
  | [::]         => fun gt => dw dt
  | [:: tw & xs] => fun gt => app (gt (dw tw))
  end.

(*|
Note that I've generalized the return type too as there was no good
reason to hardcode the definition to ``nat``. A fun exercise is to
modify the above ``app`` function and prove it equivalent to the
tactic-based version of Tej.
|*)
