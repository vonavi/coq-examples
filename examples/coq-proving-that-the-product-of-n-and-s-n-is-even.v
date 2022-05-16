(*|
############################################################
Coq: Proving that the product of ``n`` and ``(S n)`` is even
############################################################

:Link: https://stackoverflow.com/q/40791863
|*)

(*|
Question
********

Given the procedure ``even``, I want to prove that ``even (n * (S n))
= true`` for all natural numbers ``n``.

Using induction, this is easily seen to be ``true`` for the case ``n =
0``. However, the case ``(S n) * (S (S n))`` is hard to simplify.

I've considered proving the lemma that ``even (m * n) = even m /\ even
n``, but this doesn't seem to be easier.

Also, it is easy to see that if ``even n = true`` iff. ``even (S n) =
false``.
|*)

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | 1 => false
  | S (S n') => even n'
  end.

(*|
Can someone give a hint on how to prove this using a "beginner's"
subset of Coq?
|*)

(*|
Answer (Anton Trunov)
*********************

This is a case where a more advanced induction principle can be
useful. It is briefly described in `this answer
<https://stackoverflow.com/a/40595110/2747511>`__.
|*)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Lemma pair_induction (P : nat -> Prop) :
  P 0 -> P 1 -> (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros ? ? ? n. enough (P n /\ P (S n)) by tauto.
  induction n; intuition.
Qed.

(*|
Now, let's define several helper lemmas. They are obvious and can be
easily proved using the ``pair_induction`` principle and some proof
automation.
|*)

Lemma even_mul2 : forall n, Nat.even (2 * n) = true.
Proof.
  induction n; auto.
  now replace (2 * S n) with (2 + 2 * n) by ring.
Qed.

Lemma even_add_even : forall m n,
    Nat.even m = true -> Nat.even (m + n) = Nat.even n.
Proof.
  now induction m using pair_induction; auto.
Qed.

Lemma even_add_mul2 : forall m n,
    Nat.even (2 * m + n) = Nat.even n.
Proof.
  intros; apply even_add_even, even_mul2.
Qed.

Lemma even_S : forall n,
    Nat.even (S n) = negb (Nat.even n).
Proof.
  induction n; auto.
  simpl (Nat.even (S (S n))). (* not necessary -- just to make things clear *)
  apply negb_sym. assumption.
Qed.

(*|
The following lemma shows how to "distribute" ``even`` over
multiplication. It plays an important role in the proof of our main
goal. As almost always generalization helps a lot.
|*)

Lemma even_mult : forall m n,
    Nat.even (m * n) = Nat.even m || Nat.even n.
Proof.
  induction m using pair_induction; simpl; auto.
  intros n. replace (n + (n + m * n)) with (2 * n + m * n) by ring.
  now rewrite even_add_mul2.
Qed.

(*| Now, the proof of the goal is trivial |*)

Goal forall n, Nat.even (n * (S n)) = true.
  intros n. now rewrite even_mult, even_S, orb_negb_r.
Qed.

(*|
\
    Can someone give a hint on how to prove this using a "beginner's"
    subset of Coq?

You can consider this a hint, since it reveals the general structure
of a possible proof. The automatic tactics may be replaced by the
"manual" tactics like with ``rewrite``, ``apply``, ``destruct`` and so
on.
|*)

(*|
Answer (ejgallego)
******************

I'd like to contribute a shorter proof using the mathcomp lib:
|*)

From mathcomp Require Import all_ssreflect.

Lemma P n : ~~ odd (n * n.+1).
Proof. by rewrite odd_mul andbN. Qed.

(*|
``odd_mul`` is proved by simple induction, as well as ``odd_add``.

----

**A:** The definition of ``odd`` here has different structure
comparing to ``even`` in the question, that's why simple induction
works well in this case.
|*)

(*|
Answer (Anton Trunov)
*********************

Another version, in the spirit of @ejgallego's answer. Let's give
another definition for the even predicate. The purpose of this is to
make proofs by simple induction easy, so there is no need of using
``pair_induction``. The main idea is that we are going to prove some
properties of ``even2`` and then we'll use the fact that ``Nat.even``
and ``even2`` are extensionally equal to transfer the properties of
``even2`` onto ``Nat.even``.

.. coq:: none
|*)

Reset Initial.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | 1 => false
  | S (S n') => even n'
  end.

(*||*)

Require Import Coq.Bool.Bool.

Fixpoint even2 (n : nat) : bool :=
  match n with
  | O => true
  | S n' => negb (even2 n')
  end.

(*|
Let's show that ``Nat.even`` and ``even2`` are extensionally equal.
|*)

Lemma even_S n :
  Nat.even (S n) = negb (Nat.even n).
Proof. induction n; auto. apply negb_sym; assumption. Qed.

Lemma even_equiv_even2 n :
  Nat.even n = even2 n.
Proof. induction n; auto. now rewrite even_S, IHn. Qed.

(*| Some distribution lemmas for ``even2``: |*)

Lemma even2_distr_add m n :
  even2 (m + n) = negb (xorb (even2 m) (even2 n)).
Proof.
  induction m; simpl.
  - now destruct (even2 n).
  - rewrite IHm. now destruct (even2 m); destruct (even2 n).
Qed.

Lemma even2_distr_mult m n :
  even2 (m * n) = even2 m || even2 n.
Proof.
  induction m; auto; simpl.
  rewrite even2_distr_add, IHm.
  now destruct (even2 m); destruct (even2 n).
Qed.

(*|
Finally, we are able to prove our goal, using the equality between
``Nat.even`` and ``even2``.
|*)

Goal forall n, Nat.even (n * (S n)) = true.
  intros n.
  now rewrite even_equiv_even2, even2_distr_mult, orb_negb_r.
Qed.

(*|
Answer (Anton Trunov)
*********************

A short version that makes use of the standard library:
|*)

Require Import Coq.Arith.Arith.

Goal forall n, Nat.even (n * (S n)) = true.
  intros n.
  now rewrite Nat.even_mul, Nat.even_succ, Nat.orb_even_odd.
Qed.

(*|
Answer (Olivier Verdier)
************************

For what it's worth, here is my take on the solution. The essential
idea is, instead of proving a predicate ``P n``, prove instead ``P n
/\ P (S n)``, which is equivalent, but the second formulation allows
to use simple induction.

Here is the complete proof:
|*)

Require Import Nat.
Require Import Lia.

Definition claim n := even (n * (S n)) = true.

(* A technical Lemma, needed in the proof *)
Lemma tech : forall n m, even n = true -> even (n + 2 * m) = true.
Proof.
  intros. induction m.
  - simpl. replace (n + 0) with n; intuition.
  - replace (n + 2 * S m) with (S (S (n + 2 * m))); [intuition | lia].
Qed.

(* A simple identity, that Coq needs help to prove *)
Lemma ident : forall n,
    (S (S n) * S (S (S n))) = (S n * S (S n) + 2 * (S (S n))).
(* (n+2)*(n+3) = (n+1)*(n+2) + 2*(n+2) *)
Proof.
  intro.
  replace (S (S (S n))) with ((S n) + 2) by lia.
  remember (S (S n)) as m.
  replace (m * (S n + 2)) with ((S n + 2) * m) by lia.
  intuition.
Qed.

(* The claim to be proved by simple induction *)
Lemma nsn : forall n, claim n /\ claim (S n).
Proof.
  intros.
  unfold claim.
  induction n.
  - intuition.
  - intuition. rewrite ident. apply tech; auto.
Qed.
