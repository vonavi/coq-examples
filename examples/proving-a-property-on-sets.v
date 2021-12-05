(*|
##########################
Proving a property on sets
##########################

:Link: https://stackoverflow.com/questions/52448832/proving-a-property-on-sets
|*)

(*|
Question
********

As a Coq programming experience and following my question in `here
<https://stackoverflow.com/q/52195198/9335627>`__, I'd like to know if
there is another proof, possibly shorter and without using Lemma
``subset_listpair_conserve``, for proving Lemma
``subset_listpair_consFalse``. I proved it but it is long and uses
Lemma ``subset_listpair_consve``.
|*)

Require Import List.
Require Import Bool.

Definition entity := nat.
Definition entityID := nat.
Definition listPair : Set := list (entity * entityID).

(* check if e is in list l *)
Fixpoint in_listpair e (l : listPair) :=
  match l with
  | nil          => false
  | (x, y) :: l' => Nat.eqb e x || in_listpair e l'
  end.

(* check if list l1 is in list l2: i.e., 11 entities are in l2 *)
Fixpoint subset_listpair (l1 l2 : listPair) :=
  match l1 with
  | nil => true
  | (x1, _) :: l1 => in_listpair x1 l2 && subset_listpair l1 l2
  end.

Lemma subset_listpair_consver l1 l2 l3 e :
  in_listpair e l2 = true ->
  in_listpair e l3 = false ->
  subset_listpair l1 l2 = true ->
  subset_listpair l1 l3 = false.
Proof.
Admitted.

Lemma subset_listpair_consFalse l1 l2 l3 :
  subset_listpair l1 l2 = true ->
  subset_listpair l1 l3 = false -> subset_listpair l2 l3 = false.
Proof.
  induction l1.
  - induction l3.
    + destruct l2.
      * simpl. intros. inversion H0.
      * intros. destruct p. simpl in *. reflexivity.
    + simpl in *. intros. intuition. inversion H0.
  - intros. rewrite IHl1.
    + reflexivity.
    + simpl in H0. destruct a. simpl in H.
      rewrite andb_true_iff in H. rewrite andb_false_iff in H0.
      elim H. intros. assumption.
    + simpl in H0. destruct a. simpl in H.
      rewrite andb_true_iff in H. rewrite andb_false_iff in H0.
      elim H. intros.
      * elim H0.
        -- intros. pose proof subset_listpair_consver as H10.
           assert (subset_listpair l1 l3 = false) as H11.
           ++ rewrite H10 with (l2 := l2) (e := e).
              ** reflexivity.
              ** assumption.
              ** assumption.
              ** assumption.
           ++ assumption.
        -- intro. assumption.
Qed.

(*|
Answer
******

Here is one possible solution. I didn't go for a lemma-less proof or
for the shortest proof. Instead, I tried to break down everything into
a bite-sized chunks that are (relatively) easy to manipulate.

First, here is an auxiliary lemma missing from the standard library.
It simply states the law of contraposition in classical logic (we have
decidable propositions here, so those are kind of classical).
|*)

Reset subset_listpair_consFalse. (* .none *)
From Coq Require Import Arith Bool List.

Lemma contra b1 b2 :
  (b2 = false -> b1 = false) <-> (b1 = true -> b2 = true).
Proof. destruct b1, b2; intuition. Qed.

(*| Now, we will need the following easy property: |*)

Lemma in_subset_listpair {p l1 l2} :
  in_listpair p l1 = true ->
  subset_listpair l1 l2 = true ->
  in_listpair p l2 = true.
Proof.
  induction l1 as [| [x1 y1] l1 IH]; simpl; [easy |].
  rewrite orb_true_iff, andb_true_iff. intros [->%Nat.eqb_eq |] []; trivial.
  now apply IH.
Qed.

(*| Next, we prove that ``subset`` is transitive: |*)

Lemma subset_listpair_transitive l2 l1 l3 :
  subset_listpair l1 l2 = true ->
  subset_listpair l2 l3 = true ->
  subset_listpair l1 l3 = true.
Proof.
  induction l1 as [| [x1 y1] l1 IH]; simpl; trivial.
  intros [I1 S1]%andb_prop S2. rewrite (IH S1 S2), andb_true_r.
  now apply (in_subset_listpair I1).
Qed.

(*|
And now, the target lemma, which is basically a contrapositive
statement of the transitivity property:
|*)

Lemma subset_listpair_consFalse l1 l2 l3 :
  subset_listpair l1 l2 = true ->
  subset_listpair l1 l3 = false ->
  subset_listpair l2 l3 = false.
Proof.
  intros S12. rewrite contra.
  now apply subset_listpair_transitive.
Qed.
