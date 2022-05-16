(*|
###################################################
Stronger completeness axiom for real numbers in Coq
###################################################

:Link: https://stackoverflow.com/q/41326216
|*)

(*|
Question
********

Here is the completeness axiom defined in the Coq standard library.
|*)

Require Import Coq.Reals.Raxioms. (* .none *)
Print is_upper_bound. (* .unfold .messages *)
Print bound. (* .unfold .messages *)
Print is_lub. (* .unfold .messages *)
Check completeness. (* .unfold .messages *)

(*| Suppose I add in |*)

Open Scope R_scope.

Axiom supremum : forall E : R -> Prop,
    (exists l : R, is_upper_bound E l) ->
    (exists x : R, E x) ->
    {m : R | is_lub E m /\
               (forall x : R, x < m -> exists y : R, (E y /\ y > x))}.

(*|
Is this required? (i.e does it follow from the others) Would there be
any issues with consistency? Also, why is this not the definition in
the standard library (I guess this part is subjective).
|*)

(*|
Answer
******

Your ``supremum`` axiom is *equivalent* to the law of excluded middle,
in other words by introducing this axiom you are bringing classical
logic to the table.

The ``completeness`` axiom already implies a `weak form
<https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html#weak_excluded_middle>`__
of the law of excluded middle, as shown by the means of the
``sig_not_dec`` lemma (`Rlogic
<https://coq.inria.fr/library/Coq.Reals.Rlogic.html>`__ module), which
states the decidability of negated formulas:
|*)

Require Import Coq.Reals.Rlogic. (* .none *)
Check sig_not_dec. (* .unfold .messages *)

(*|
``supremum`` axiom implies LEM
==============================

Let's use the standard proof of the ``sig_not_dec`` lemma to show that
with the stronger completeness axiom (``supremum``) we can derive the
strong form of the law of excluded middle.
|*)

Require Import Coq.Reals.RIneq.

Lemma supremum_implies_lem : forall P : Prop, P \/ ~ P.
Proof.
  intros P.
  set (E := fun x => x = 0 \/ (x = 1 /\ P)).
  destruct (supremum E) as (x & H & Hclas).
  exists 1. intros x [->|[-> _]].
  apply Rle_0_1. apply Rle_refl. exists 0; now left.
  destruct (Rle_lt_dec 1 x) as [H'|H'].
  - left.
    pose proof (Rlt_le_trans 0 1 x Rlt_0_1 H') as Hx0.
    destruct (Hclas 0 Hx0) as (y & [contra | (_ & Hp)] & Hy0).
    + now apply Rgt_not_eq in Hy0.
    + exact Hp.
  - right. intros HP.
    apply (Rlt_not_le _ _ H'), H; now right.
Qed.

(*|
LEM implies ``supremum`` axiom
==============================

Now, let us show that the strong version of LEM implies the
``supremum`` axiom. We do this by showing that in *constructive*
setting we can derive a *negated* form of ``supremum`` where the
``exists y:R, E y /\ y > x`` part gets replaced with ``~ (forall y, y
> x -> ~ E y)``, and then using the usual classical facts we show that
the original statement holds as well.
|*)

Reset supremum. (* .none *)
Require Import Coq.Reals.RIneq. (* .none *)
Require Import Classical.

Lemma helper (z : R) (E : R -> Prop) :
  (forall y, y > z -> ~ E y) -> is_upper_bound E z.
Proof.
  intros H x Ex.
  destruct (Rle_dec x z).
  - assumption.
  - specialize (H x (Rnot_le_gt x z n)); contradiction.
Qed.

Lemma supremum : forall E : R -> Prop,
    (exists l : R, is_upper_bound E l) ->
    (exists x : R, E x) ->
    {m : R | is_lub E m /\ (forall x : R, x < m -> exists y : R, E y /\ y > x)}.
Proof.
  intros E Hbound Hnonempty.
  pose proof (completeness E Hbound Hnonempty) as [m Hlub].
  clear Hbound Hnonempty.
  exists m. split; auto.
  intros x Hlt.
  assert (~ (forall y, y > x -> ~ E y)) as Hclass.
  intro Hcontra; apply helper in Hcontra.
  destruct Hlub as [Hup Hle].
  specialize (Hle x Hcontra).
  apply Rle_not_lt in Hle; contradiction.
  (* classical part starts here *)
  apply not_all_ex_not in Hclass as [y Hclass]; exists y.
  apply imply_to_and in Hclass as [Hyx HnotnotEy].
  now apply NNPP in HnotnotEy.
Qed.
