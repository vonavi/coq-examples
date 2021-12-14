(*|
#################################################################
How to prove decidability of a partial order inductive predicate?
#################################################################

:Link: https://stackoverflow.com/questions/50390613/how-to-prove-decidability-of-a-partial-order-inductive-predicate
|*)

(*|
Question
********

Minimal executable example
==========================
|*)

Require Import Setoid.

Ltac inv H := inversion H; clear H; subst.

Inductive t : Set := A | B | C.

Ltac destruct_ts :=
  repeat match goal with
         | [ x : t |- _ ] => destruct x
         end.

Inductive le : t -> t -> Prop :=
| le_refl : forall x, le x x
| le_trans : forall x y z, le x y -> le y z -> le x z
| le_A_B : le A B
| le_B_C : le B C.

Definition leb (x y : t) : bool :=
  match x, y with
  | A, _ => true
  | _, C => true
  | B, B => true
  | _, _ => false
  end.

Theorem le_iff_leb : forall x y,
    le x y <-> leb x y = true.
Proof.
  intros x y. split; intro H.
  - induction H; destruct_ts; simpl in *; congruence.
  - destruct_ts; eauto using le; simpl in *; congruence.
Qed.

Theorem le_antisym : forall x y,
    le x y -> le y x -> x = y.
Proof.
  intros x y H1 H2.
  rewrite le_iff_leb in *. (* How to prove that without using [leb]? *)
  destruct x, y; simpl in *; congruence.
Qed.

Theorem le_dec : forall x y, { le x y } + { ~le x y }.
  intros x y. destruct x, y; eauto using le.
  - apply right. intros H. (* Stuck here *)
    inv H. rewrite le_iff_leb in *.
    destruct y; simpl in *; congruence.
  - apply right. intros H. (* Same thing *)
    inv H. rewrite le_iff_leb in *.
    destruct y; simpl in *; congruence.
  - apply right. intros H. (* Same thing *)
    inv H. rewrite le_iff_leb in *.
    destruct y; simpl in *; congruence.
Qed.

(*|
Context
=======

I am trying to define the partial order ``A <= B <= C`` with a
relation ``le`` in Coq and prove that it is decidable: ``forall x y,
{le x y} + {~le x y}``.

I succeeded to do it through an equivalent boolean function ``leb``
but cannot find a way to prove it directly (or ``le_antisym`` for that
mater). I get stuck in situations like the following:

.. coq:: none
|*)

Reset le_dec.
Theorem le_dec : forall x y, { le x y } + { ~le x y }.
  intros x y. destruct x, y; eauto using le.
  - apply right.

(*||*)

    intros H. (* .unfold .no-in *)
Abort. (* .none *)

(*|
Questions
=========

1. How can I prove, that ``le B A`` is a false premise?
2. Is there an other other proof strategy that I should use?
3. Should I define my predicate ``le`` differently?
|*)

(*|
Answer
******

I'd also go with Arthur's solution. But let me demonstrate another
approach.

First, we'll need a couple of supporting lemmas:
|*)

Lemma not_leXA x : x <> A -> ~ le x A.
Proof. remember A; intros; induction 1; subst; firstorder congruence. Qed.

Lemma not_leCX x : x <> C -> ~ le C x.
Proof. remember C; intros; induction 1; subst; firstorder congruence. Qed.

(*| Now we can define ``le_dec``: |*)

Definition le_dec x y : { le x y } + { ~le x y }.
Proof.
  destruct x, y; try (left; abstract constructor).
  - left; abstract (eapply le_trans; constructor).
  - right; abstract now apply not_leXA.
  - right; abstract now apply not_leCX.
  - right; abstract now apply not_leCX.
Defined.

(*|
Notice that I used ``Defined`` instead of ``Qed`` -- now you can
calculate with ``le_dec``, which is usually the point of using the
``sumbool`` type.

I also used ``abstract`` to conceal the proof terms from the
evaluator. E.g. let's imagine I defined a ``le_dec'`` function which
is the same as ``le_dec``, but with all ``abstract`` removed, then we
would get the following results when trying to compute ``le_dec B A``
/ ``le_dec' B A``:
|*)

Compute le_dec B A. (* .unfold *)

(*| .. coq:: none |*)

Definition le_dec' x y : { le x y } + { ~le x y }.
Proof.
  destruct x, y; try (left; constructor).
  - left; eapply le_trans; constructor.
  - right; now apply not_leXA.
  - right; now apply not_leCX.
  - right; now apply not_leCX.
Defined.

(*| and |*)

Compute le_dec' B A. (* .unfold *)
