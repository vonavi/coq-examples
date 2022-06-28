(*|
#######################################################
Abstracting leads to a term ill-typed... yet well-typed
#######################################################

:Link: https://stackoverflow.com/q/14867685
|*)

(*|
Question
********

I was stuck on a problem for a while, for which I derived a smaller
standalone example:
|*)

Axiom f : nat -> Set.

Goal forall (n : nat) (e : n = n) (x : f n),
    match e in _ = _n return f _n -> Prop with
    | Logic.eq_refl => fun v : f n => v = x
    end x.

(*|
Now, if you try to ``destruct e``, you get the following error
message:
|*)

  Fail destruct e. (* .unfold .messages *)
Abort. (* .none *)

(*|
After scratching my head for a while, I couldn't figure out what was
ill-typed in that term... So I tried this:
|*)

Definition illt :=
  fun (n : nat) (e : n = n) =>
    forall x : f n,
      match e in _ = _n return f _n -> Prop with
      | Logic.eq_refl => fun v : f n => v = x
      end x.

(*| And Coq accepts it, at type |*)

Check illt. (* .unfold .messages *)

(*|
So, what is wrong with this error message, and how could I solve/tweak
my initial goal?

----

EDIT: To address Robin Green's comment, here is the ``Set Printing
All`` versions of the error message:

.. coq:: none
|*)

Set Printing All.

Goal forall (n : nat) (e : n = n) (x : f n),
    match e in _ = _n return f _n -> Prop with
    | Logic.eq_refl => fun v : f n => v = x
    end x.

(*||*)

  Fail destruct e. (* .unfold .messages *)
Abort. (* .none *)

(*| It is a well-typed term, and nothing is implicit. |*)

(*|
Answer
******

Here is a possible explanation of the problem. What happens when
constructing a pattern-matching construct can also be described using
a theorem. Here is my view of the theorem that is being used in your
case.
|*)

Reset Initial. (* .none *)
Axiom f : nat -> Set. (* .none *)
Check eq_rect. (* .unfold *)

(*|
So when pattern matching on an equality, you have to provide a formula
``P`` parametrized on **any value** ``y`` that happens to be provably
equal to ``x``. Intuitively, you should be able to replace your
pattern-matching expression by ``apply eq_rect``, but the property
``P`` that should come up there is beyond the reach of what Coq can
guess, because every occurrence of ``x`` in your formula is bound to
be in type ``f n`` and cannot just be in type ``f m`` where ``m = n``.
The error message does not say that, it is probably a mistake.

To perform your proof, I suggest rather to use the fact that proofs of
equality are unique in certain classes of types, and ``nat`` belongs
to such a class. This is treated in the file ``Eqdep_dec``.
|*)

Require Eqdep_dec Arith.

(*| Now your proof goes through quite easily. |*)

Goal forall n (x : f n) (e : n = n),
    match e in _ = _n return f _n -> Prop with
    | Logic.eq_refl => fun v : f n => v = x
    end x.
  intros n x e. replace e with (eq_refl n).
  - reflexivity.
  - apply Eqdep_dec.UIP_dec, PeanoNat.Nat.eq_dec.
Qed.

(*|
Now, this solution may feel unsatisfactory. Where does this
``UIP_dec`` come from? UIP stands for *uniqueness of identity proofs*
and unfortunately, this property is not guaranteed for all arbitrary
types. It is guaranteed for all types where equality is decidable (as
expressed by ``UIP_dec``), for instance ``nat``.
|*)
