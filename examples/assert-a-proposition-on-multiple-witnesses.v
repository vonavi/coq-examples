(*|
##########################################
Assert a proposition on multiple witnesses
##########################################

:Link: https://stackoverflow.com/q/54093713
|*)

(*|
Question
********

Assume I have an existential proposition ``P`` about the natural
numbers, for example
|*)

Definition P (n : nat) : Prop := exists k : nat, True.

(*| Assume also that I have proved ``P`` for all numbers, |*)

Lemma allP : forall n : nat, P n.
Proof.
  intros. exists 0. trivial.
Defined.

(*|
Then I have a witness ``k`` for all ``n`` (``k`` is always 0 in the
previous example) and I want to assert something about all ``k``\ s,
such as
|*)

Fail Definition allWitnessesBelowOne : Prop :=
  forall n : nat,
    match allP n with
    | ex_intro _ k _ => k <= 1
    end. (* .unfold .fails *)

(*|
except this does not compile, I get the above error. I don't
understand what is of sort ``Type`` here, everything looks in
``Prop``. I am only trying to build a proof, why isn't Coq happy? In
my complete problem, ``P`` is much more complicated and it does make
sense to prove something about all witnesses.

----

**A (eponier):** This is ``Prop`` that is in ``Type``! ``k <= 1`` has
type ``Prop`` which is not in ``Prop``. Instead, for instance, ``I``
is a proof of ``True`` which is in ``Prop``. I don't known how to
solve your problem, however.
|*)

(*|
Answer
******

Elaborating on @eponier's comment, when you write
|*)

Fail Definition allWitnessesBelowOne : Prop :=
  forall n : nat,
    match allP n with
    | ex_intro _ k _ => k <= 1
    end. (* .fails *)

(*| you are actually writing |*)

Fail Definition allWitnessesBelowOne : Prop :=
  forall n : nat,
    match allP n return Prop with
    | ex_intro _ k _ => k <= 1
    end. (* .fails *)

(*|
When you have ``return Prop``, the return type ``Prop`` has type
``Type``, while it must have type ``Prop`` to satisfy the elimination
restriction. Basically, if you lift this restriction, you make Coq
inconsistent with classical logic. See, for example, `the official
documentation of Prop
<https://coq.inria.fr/refman/language/cic.html#inference-prop>`__,
`Incorrect elimination of X in the inductive type "or":
<https://stackoverflow.com/questions/32261254/incorrect-elimination-of-x-in-the-inductive-type-or>`__,
or `CPDT on universes
<http://adam.chlipala.net/cpdt/html/Universes.html>`__.

Another way of looking at this is that, if you do not have any axioms,
it must be possible to interpret all ``Prop``\ s as either the
singleton set (if they are true) or the empty set (if they are false).
There is no non-constant function out of a singleton set, so you
cannot define any interesting properties over a proof of ``exists k :
nat, True``.

The simplest way to fix this is to stop using ``Prop``. Instead use
sigma (``sig``) types to say:
|*)

Reset Initial. (* .none *)
Definition P (n : nat) := { k : nat | True }.

Lemma allP : forall n : nat, P n.
Proof.
  intros. exists 0. trivial.
Defined.

Definition allWitnessesBelowOne : Prop :=
  forall n : nat,
    match allP n with
    | exist _ k _ => k <= 1
    end.

(*| An alternative definition of this last one is |*)

Reset allWitnessesBelowOne. (* .none *)
Definition allWitnessesBelowOne : Prop :=
  forall n : nat,
    proj1_sig (allP n) <= 1.

(*|
----

The other thing you can do is that you can do everything continuation
passing style:
|*)

Reset Initial. (* .none *)
Definition P (n : nat) : Prop := exists k:nat, True.

Lemma allP : forall n : nat, P n.
Proof.
  intros. exists 0. trivial.
Defined.

Lemma allWitnessesBelowOne_cps
      (n : nat)
      (Result : P n -> Prop)
  : (forall k pf, k <= 1 -> Result (ex_intro _ k pf))
    -> Result (allP n).
Proof.
  unfold allP; intro H.
  apply H; repeat constructor.
Defined.

(*|
Here, ``Result`` determines the ``Prop`` that you'll ultimately be
proving. This lemma says that whenever you're trying to prove a
``Result`` about ``allP n``, you can assume that you're proving a
``Result`` about a value that is ``<= 1``. This is rather complicated,
though, so I would suggest just dropping ``Prop`` if you can manage
it.
|*)
