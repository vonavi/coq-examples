(*|
######################
Mathematical induction
######################

Many problems are formulated inductively. For instance, we can
formulate the relation of subset in the following manner:
|*)

Require Import List.
Import ListNotations.

Inductive subseq {X : Type} : list X -> list X -> Prop :=
| empty_subseq : subseq [] []
| subseq_left_elim : forall (l1 l2 : list X) (x : X),
    subseq (x :: l1) l2 -> subseq l1 l2
| subseq_intro : forall (l1 l2 : list X) (x : X),
    subseq l1 l2 -> subseq (x :: l1) (x :: l2).

Notation "l <<< k" := (subseq l k) (at level 10, only parsing).

(*|
The above function ``subseq`` postulates that the first argument is a
subset of the second one. Its formulation does not look hard and is
based on three facts:

1. One empty set is a subset of another empty set (this fact is
   reflected by constructor ``empty_subseq``).
2. After the deletion of an element from a set, the set remains to be
   a subset of another set (property ``subseq_left_elim``).
3. The addition of the same element into two sets does not change the
   subset relation (property ``subseq_intro``).

Let us notice that the user describes the desired property in the form
that he understands in the best way. Should user's formulation suit
the induction principle? Actually, no one guarantee that. To
demonstrate this fact, we try to show a proof of the subset relation
using the properties mentioned above:
|*)

Goal [1; 3; 5] <<< [0; 1; 2; 3; 4; 5; 6].
Proof.
  apply subseq_left_elim with 0. apply subseq_intro. apply subseq_intro.
  apply subseq_left_elim with 2. apply subseq_intro. apply subseq_intro.
  apply subseq_left_elim with 4. apply subseq_intro. apply subseq_intro.
  apply subseq_left_elim with 6. apply subseq_intro. apply empty_subseq.
Qed.

(*|
On one hand, a prove by mathematical induction is based on some
decreasing parameter. Usually, in the case of sets, we expect that the
size of a set decreases on every step. On the other hand, in our
example, there is no such set (moreover, the size of inner set
eventually increases). So, the mathematical induction cannot be apply
here. But the user is sure that his formulation of the subset property
is totally correct. How can we confirm his assurance by a proof?

In fact, we can try to reformulate this property:
|*)

Inductive subseq' {X : Type} : list X -> list X -> Prop :=
| subseq_empty : subseq' [] []
| subseq_drop_right l1 l2 x : subseq' l1 l2 -> subseq' l1 (x :: l2)
| subseq_drop_both l1 l2 x : subseq' l1 l2 -> subseq' (x :: l1) (x :: l2).
#[local] Hint Constructors subseq' : core.

(*|
Here, we just changed the second property: an addition of element into
the outer set does not influence the subset property. Intuitively,
function ``subseq'`` should give the same relation as ``subseq`` does.
First of all, let us check how this new property works on the same
example:
|*)

Goal subseq' [1; 3; 5] [0; 1; 2; 3; 4; 5; 6].
  apply subseq_drop_right. apply subseq_drop_both.
  apply subseq_drop_right. apply subseq_drop_both.
  apply subseq_drop_right. apply subseq_drop_both.
  apply subseq_drop_right. apply subseq_empty.
Qed.

(*|
I hope that the attentive reader has already noted the difference: the
size of outer set decreases on every step. That is a good mark to
apply for the induction principle.
|*)

Lemma subseq_equiv' : forall {X : Type} (l1 l2 : list X),
    subseq' l1 l2 -> subseq l1 l2.
Proof.
  intros X l1 l2 H. induction H.
  - constructor.
  - apply (subseq_left_elim _ _ x).
    now apply (subseq_intro _ _ x) in IHsubseq'.
  - now apply (subseq_intro _ _ x) in IHsubseq'.
Qed.


Lemma subseq_remove : forall {X : Type} (x : X) (l1 l2 : list X),
    subseq' (x :: l1) l2 -> subseq' l1 l2.
Proof.
  intros * H.
  remember (x :: l1) as l; revert l1 Heql.
  induction H; intros l [=].
  - constructor. now apply IHsubseq'.
  - subst l. auto.
Qed.

Lemma subseq_equiv : forall {X : Type} (l1 l2 : list X),
    subseq l1 l2 -> subseq' l1 l2.
Proof.
  intros * H. induction H; auto.
  now apply subseq_remove in IHsubseq.
Qed.


Lemma subseq_trans' : forall {X : Type} (l1 l2 l3 : list X),
    subseq' l1 l2 -> subseq' l2 l3 -> subseq' l1 l3.
Proof.
  intros * H H0; revert l1 H. induction H0; intros l H.
  - inversion H. auto.
  - apply IHsubseq' in H. auto.
  - inversion H.
    + apply IHsubseq' in H3. auto.
    + apply IHsubseq' in H3. auto.
Qed.


Reset Initial. (* .none *)

Require Import Arith.

Inductive dfa_states := Lt | Eq | Gt.

Inductive dfa : nat -> nat -> dfa_states -> Type :=
| eq_zero : dfa O O Eq
| lt_zero : forall n, dfa O (S n) Lt
| gt_zero : forall n, dfa (S n) O Gt
| st_succ : forall n m c, dfa n m c -> dfa (S n) (S m) c.
#[local] Hint Constructors dfa : core.

Inductive dfa' : nat -> nat -> dfa_states -> Type :=
| eq_n  : forall n, dfa' n n Eq
| lt_n  : forall n, dfa' n (S n) Lt
| gt_n  : forall n, dfa' (S n) n Gt
| lt_Sm : forall n m, dfa' n m Lt -> dfa' n (S m) Lt
| gt_Sn : forall n m, dfa' n m Gt -> dfa' (S n) m Gt.
#[local] Hint Constructors dfa' : core.

Lemma dfa_equiv : forall n m c, dfa n m c -> dfa' n m c.
Proof.
  intros n m c H. induction H.
  - auto.
  - induction n; auto.
  - induction n; auto.
  - clear H. induction IHdfa; auto.
Qed.

Lemma dfa_equiv' : forall n m c, dfa' n m c -> dfa n m c.
Proof.
  intros n m c H. induction H.
  - induction n; auto.
  - induction n; auto.
  - induction n; auto.
  - clear H. revert n IHdfa'.
    induction m; intros n H; inversion H.
    + auto.
    + constructor. now apply IHm.
  - clear H. revert m IHdfa'.
    induction n; intros m H; inversion H.
    + auto.
    + constructor. now apply IHn.
Qed.


Lemma dfa_st_eq : forall n m c c', dfa n m c -> dfa n m c' -> c = c'.
Proof.
  induction n; destruct m.
  all: intros c c' H H0; inversion H; inversion H0.
  all: try reflexivity. now apply (IHn m).
Qed.

Lemma dfa_st_eq' : forall n m c c', dfa' n m c -> dfa' n m c' -> c = c'.
Proof.
  intros n m c c' H H0. apply dfa_equiv' in H. apply dfa_equiv' in H0.
  now apply (dfa_st_eq n m).
Qed.


Lemma dfa_eq_spec : forall n, dfa n n Eq.
Proof.
  induction n; auto.
Qed.

Lemma dfa_eq_spec' : forall n, dfa' n n Eq.
Proof.
  auto.
Qed.

Lemma dfa_lt_spec : forall n m, n < m -> dfa n m Lt.
Proof.
  induction n; destruct m; intro H.
  - contradiction (Nat.nlt_0_r 0).
  - auto.
  - contradiction (Nat.nlt_0_r (S n)).
  - apply lt_S_n, IHn in H. auto.
Qed.

Lemma dfa_lt_spec' : forall n m, n < m -> dfa' n m Lt.
Proof.
  induction m; intro H.
  - contradiction (Nat.nlt_0_r n).
  - apply lt_n_Sm_le, le_lt_eq_dec in H. destruct H as [H | H].
    + apply IHm in H. auto.
    + now subst n.
Qed.

Lemma dfa_gt_spec : forall n m, n > m -> dfa n m Gt.
Proof.
  induction n; destruct m; intro H.
  - contradiction (Nat.nlt_0_r 0).
  - contradiction (Nat.nlt_0_r (S m)).
  - auto.
  - apply lt_S_n, IHn in H. auto.
Qed.

Lemma dfa_gt_spec' : forall n m, n > m -> dfa' n m Gt.
Proof.
  intros n m. induction n; intro H.
  - contradiction (Nat.nlt_0_r m).
  - apply lt_n_Sm_le, le_lt_eq_dec in H. destruct H as [H | H].
    + apply IHn in H. auto.
    + now subst n.
Qed.
