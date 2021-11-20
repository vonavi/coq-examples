(*|
Abstracting patterns in induction rule for inductive predicates for Coq
=======================================================================

:Link: https://stackoverflow.com/questions/60027551/abstracting-patterns-in-induction-rule-for-inductive-predicates-for-coq
|*)

(*|
Question
--------

Consider the following proposition in Coq:
|*)

Require Import List.
Import ListNotations.

Inductive subseq : list nat -> list nat -> Prop :=
 | nil_s : forall (l: list nat), subseq nil l
 | cons_in l1 l2 x (H: subseq l1 l2) : subseq (x :: l1) (x :: l2)
 | cons_nin l1 l2 x (H: subseq l1 l2) : subseq l1 (x :: l2).

Lemma subseq_remove_rewritten: forall (x: nat) (l1' l1 l2 : list nat),
    subseq l1' l2 -> l1' = (x :: l1) -> subseq l1 l2.
Proof.
  intros x l1' l1 l2 H1 H2. induction H1.
  - discriminate.
  - injection H2 as H3 H4. rewrite H4 in H1. apply cons_nin. apply H1.
  - apply IHsubseq in H2. apply cons_nin. apply H2.
Qed.

Lemma subseq_remove: forall (x: nat) (l1 l2 : list nat),
  subseq (x :: l1) l2 -> subseq l1 l2.
Proof.
  intros x l1 l2 H.
  apply subseq_remove_rewritten with (x:=x) (l1':=x :: l1).
  - apply H.
  - reflexivity.
Qed.

(*|
I worked in Isabelle before Coq. There originally, the induction
tactic could not solve directly this goal and the trick was to come up
with a lemma like `subseq_remove_rewritten` and then prove the
original goal. This is the situation in the manual Isabelle/HOL: A
Proof Assistant for Higher-Order Logic. Later, the tactic became
smarter and one can write patterns in which to abstract on. So the
proof is written like this:

::

    lemma
      assumes "subseq (x # l1) l2"
      shows "subseq l1 l2"
      using assms
      apply(induction "x # l1" "l2" rule: subseq.induct)
        apply simp
       apply(intro subseq.intros(3),simp)
      by (intro subseq.intros(3))

I was wondering if Coq has a similar way to avoid proving a lemma like
`subseq_remove_rewritten` and go directly to prove `subseq_remove`.
|*)

(*|
Answer
------

You can use the `dependent induction` tactic (documented `here
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.dependent-induction>`_).
For example:
|*)

Reset subseq. (* .none *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Equality. (* Needed to use the tactic *)

Inductive subseq : list nat -> list nat -> Prop :=
| nil_s : forall (l: list nat), subseq nil l
| cons_in l1 l2 x (H: subseq l1 l2) : subseq (x :: l1) (x :: l2)
| cons_nin l1 l2 x (H: subseq l1 l2) : subseq l1 (x :: l2).

Lemma subseq_remove: forall (x: nat) (l1 l2 : list nat),
  subseq (x :: l1) l2 -> subseq l1 l2.
Proof.
  intros x l1 l2 H. dependent induction H generalizing x.
  - now apply cons_nin.
  - eauto using cons_nin.
Qed.

(*|
Unfortunately, though this tactic has been around for a while, it is
still described as experimental in the reference manual, and I don't
know if the Coq developers have any plans of improving it in the
future. It has a few deficiencies, such as not allowing the user to
name the variables and hypotheses used in the induction proof. I
personally prefer to add the equality assumptions to the proof myself,
as in your first attempt, or to reformulate the definition of `subseq`
as a `Fixpoint`, so that you can invert the hypothesis by
simplification. For example:
|*)

Reset subseq. (* .none *)
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint subseq (l1 l2 : list nat) : Prop :=
  match l1, l2 with
  | [], _ => True
  | x1 :: l1, [] => False
  | x1 :: l1, x2 :: l2 => x1 = x2 /\ subseq l1 l2 \/ subseq (x1 :: l1) l2
  end.

Lemma subseq_nin x2 l1 l2 : subseq l1 l2 -> subseq l1 (x2 :: l2).
Proof. destruct l1 as [|x1 l1]; simpl; eauto. Qed.

Lemma subseq_remove : forall (x: nat) (l1 l2 : list nat),
  subseq (x :: l1) l2 -> subseq l1 l2.
Proof.
  intros x l1 l2 H.
  induction l2 as [|x2 l2 IH]; try easy.
  destruct H as [[<- H]|H]; eauto using subseq_nin.
Qed.
