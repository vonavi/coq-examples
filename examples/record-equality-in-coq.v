(*|
######################
Record equality in coq
######################

:Link: https://stackoverflow.com/q/50924127
|*)

(*|
Question
********

For example I have this sample record:
|*)

Require Import ZArith. (* .none *)
Record Sample := {
    SA :> nat;
    SB :> Z;
    SCond : Z.abs_nat SB <> SA
  }.

(*| When I want to proof this Lemma: |*)

Lemma Sample_eq : forall a b : Sample, a = b <-> SA a = SA b /\ SB a = SB b.

(*| I see this: |*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
Question 1: How to force Coq to show SA a instead of a?

Question 2: How to proof this Lemma?
|*)

(*|
Answer
******

Question 1
==========

Coq prints ``SA`` because you declared it as a coercion. You can
prevent this by adding the option ``Set Printing Coercions.`` to your
file. As far as I know, there is no way of just making Coq print only
``SA`` but not other coercions such as ``SB``. You can, however,
replace the ``:>`` by ``:`` to prevent ``SA`` from being declared as a
coercion.

Question 2
==========

Your lemma cannot be proved without assuming extra axioms into Coq's
theory. The problem is that you need to show that two proofs of
``Z.abs_nat SB <> SA`` are equal in order to show that two records of
type ``Sample`` are equal, and there is nothing in Coq's theory that
can help you with that. You have two options:

1. Use the axiom of proof irrelevance, which says ``forall (P : Prop)
   (p1 p2 : P), p1 = p2``. For example:
|*)

Reset Initial. (* .none *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ProofIrrelevance.

Record Sample := {
    SA : nat;
    SB : Z;
    SCond : Z.abs_nat SB <> SA
  }.

Lemma Sample_eq a b : SA a = SA b -> SB a = SB b -> a = b.
Proof.
  destruct a as [x1 y1 p1], b as [x2 y2 p2]. simpl.
  intros e1 e2. revert p1 p2.
  rewrite <- e1, <- e2. intros p1 p2.
  now rewrite (proof_irrelevance _ p1 p2).
Qed.

(*|
   (Note the calls to ``revert``: they are needed to prevent dependent
   type errors when rewriting with ``e1`` and ``e2``.)

2. Replace inequality with a proposition for which proof irrelevance
   is valid without extra axioms. A typical solution is to use a
   boolean version of the proposition. The ``DecidableEqDepSet``
   module shows that the proofs of equality for a type that has
   decidable equality, such as the booleans, satisfies proof
   irrelevance.
|*)

Reset Initial. (* .none *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Eqdep_dec.

Module BoolDecidableSet <: DecidableSet.

  Definition U := bool.
  Definition eq_dec := Bool.bool_dec.

End BoolDecidableSet.

Module BoolDecidableEqDepSet := DecidableEqDepSet BoolDecidableSet.

Record Sample := {
    SA : nat;
    SB : Z;
    SCond : Nat.eqb (Z.abs_nat SB) SA = false
  }.

Lemma Sample_eq a b : SA a = SA b -> SB a = SB b -> a = b.
Proof.
  destruct a as [x1 y1 p1], b as [x2 y2 p2]. simpl.
  intros e1 e2. revert p1 p2.
  rewrite <- e1, <- e2. intros p1 p2.
  now rewrite (BoolDecidableEqDepSet.UIP _ _ p1 p2).
Qed.
