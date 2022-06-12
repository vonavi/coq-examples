(*|
###########################################################
How to prove False from obviously contradictory assumptions
###########################################################

:Link: https://stackoverflow.com/q/29286679
|*)

(*|
Question
********

Suppose I want to prove following Theorem:
|*)

Theorem succ_neq_zero : forall n m: nat, S n = m -> 0 = m -> False.
Abort. (* .none *)

(*|
This one is trivial since ``m`` cannot be both successor and zero, as
assumed. However I found it quite tricky to prove it, and I don't know
how to make it without an auxiliary lemma:
|*)

Lemma succ_neq_zero_lemma : forall n : nat, O = S n -> False.
Proof. intros. inversion H. Qed.

Theorem succ_neq_zero : forall n m : nat, S n = m -> 0 = m -> False.
Proof.
  intros. symmetry in H.
  apply (succ_neq_zero_lemma n). transitivity m.
  - assumption.
  - assumption.
Qed.

(*|
I am pretty sure there is a better way to prove this. What is the best
way to do it?
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

You just need to substitute for ``m`` in the first equation:
|*)

Reset Initial. (* .none *)
Theorem succ_neq_zero : forall n m : nat, S n = m -> 0 = m -> False.
Proof.
  intros n m H1 H2. rewrite <- H2 in H1. inversion H1.
Qed.

(*|
----

**A:** Or a bit more concise yet still explicit:
|*)

Reset Initial. (* .none *)
Theorem succ_neq_zero : forall n m : nat, S n = m -> 0 = m -> False.
Proof.
  intros n m H <-. discriminate H.
Qed.

(*| less explicit works too: |*)

Reset Initial. (* .none *)
Theorem succ_neq_zero : forall n m : nat, S n = m -> 0 = m -> False.
Proof.
  intros. subst. discriminate.
Qed.

(*|
Answer (Gilles 'SO- stop being evil')
*************************************

There's a very easy way to prove it:
|*)

Reset Initial. (* .none *)
Theorem succ_neq_zero : forall n m : nat, S n = m -> 0 = m -> False.
Proof.
  congruence.
Qed.

(*|
The ``congruence`` tactic is a decision procedure for ground
equalities on uninterpreted symbols. It's complete for uninterpreted
symbols and for constructors, so in cases like this one, it can prove
that the equality ``0 = m`` is impossible.
|*)

(*|
Answer (larsr)
**************

It might be useful to know how congruence works.

To prove that two terms constructed by different constructors are in
fact different, just create a function that returns ``True`` in one
case and ``False`` in the other cases, and then use it to prove ``True
= False``. I think this is explained in `Coq'Art
<https://www.labri.fr/perso/casteran/CoqArt/>`__
|*)

Example not_congruent : 0 <> 1.
Proof.
  intros C. (* now our goal is 'False' *)
  pose (fun m => match m with 0 => True | S _ => False end) as f.
  assert (Contra: f 1 = f 0) by (rewrite C; reflexivity).
  now replace False with True by Contra.
Qed.
