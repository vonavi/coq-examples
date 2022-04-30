(*|
##################################
Proving increasing ``iota`` in Coq
##################################

:Link: https://stackoverflow.com/q/45268498
|*)

(*|
Question
********

I am stuck on a goal.

Assume we have the following definition:

.. coq:: none
|*)

Require Import PeanoNat.
Require Import List.
Import ListNotations.

(*||*)

Fixpoint iota (n : nat) : list nat :=
  match n with
  | 0   => []
  | S k => iota k ++ [k]
  end.

(*| I use these two lemmas, proofs omitted: |*)

Axiom app_split : forall A x (l l2 : list A),
    In x (l ++ l2) -> not (In x l2) -> In x l.
Axiom s_inj : forall n, ~(n = S n).

(*| And we want to prove: |*)

Theorem t1 : forall n, In n (iota n) -> False.

(*| So far, I have managed to the following: |*)

Reset t1. (* .none *)
Theorem t1 : forall n, In n (iota n) -> False.
Proof.
  intros. induction n.
  - cbn in H. contradiction.
  - cbn in H. apply app_split in H.
    2:{ unfold not. intros.
        unfold In in H0. destruct H0.
        + assert (~(n = S n)) by now apply s_inj. contradiction.
        + apply H0. }
    1:{ apply IHn.
Abort.

(*|
However, I am completely stuck, I need to somehow show that: ``In n
(iota n)`` assuming ``In (S n) (iota n)``.
|*)

(*|
Answer
******

As you've observed the fact that the ``n`` in ``In n`` and the one in
``iota n`` are in lockstep in your statement makes the induction
hypothesis hard to invoke (if not completely useless).

The trick here is to prove a more general statement than the one you
are actually interested in which breaks this dependency between the
two ``n``\ s. I would suggest:
|*)

Theorem t : forall n k, n <= k -> In k (iota n) -> False.
Proof.
  intro n; induction n; intros k nlek kin.
  - cbn in kin; contradiction.
  - cbn in kin; apply app_split in kin.
    + eapply IHn with (k := k).
      * transitivity (S n); eauto.
      * assumption.
    + inversion 1; subst.
      * apply (Nat.nle_succ_diag_l _ nlek).
      * contradiction.
Qed.

(*| from which you can derive ``t1`` as a corollary: |*)

Corollary t1 : forall n, In n (iota n) -> False.
  intro n; apply (t n n); reflexivity.
Qed.

(*|
If you want to peek at the proof of ``t``, you can `have a look at
this self-contained gist
<https://gist.github.com/gallais/83e84596e08b15dfa605b2d7c696f734>`__

----

**Q:** Interesting - how does one get the intuition for when
something's impossible to prove with its current formulation - is it
that either some of the assumptions or the inductive hypothesis would
be directly (or indirectly) in contradiction with the conclusion? Or
is there a notion of "not sufficient / strong" enough inductive
hypothesis? How can one tell? (This is obvious once you show me, but
figuring this out myself...)

**A:** Experience mostly. But whenever two things are in lockstep or
one value is fixed to be a constant and that prevents you from using
the induction hypothesis, that's a strong smell that you may want to
look for a more general statement. `This blog post
<https://homes.cs.washington.edu/~jrw12/InductionExercises.html>`__
sets up a number of exercises where you have to generalize the
induction hypothesis to make it work. You may want to look into it.
|*)
