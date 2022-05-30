(*|
###############################################
How to use a custom induction principle in Coq?
###############################################

:Link: https://stackoverflow.com/q/33071903
|*)

(*|
Question
********

I read that the induction principle for a type is just a theorem about
a proposition ``P``. So I constructed an induction principle for
``List`` based on the right (or reverse) list constructor.
|*)

Definition rcons {X : Type} (l : list X) (x : X) : list X :=
  l ++ x :: nil.

(*| The induction principle itself is: |*)

Definition true_for_nil {X : Type} (P : list X -> Prop) : Prop :=
  P nil.

Definition true_for_list {X : Type} (P : list X -> Prop) : Prop :=
  forall xs, P xs.

Definition preserved_by_rcons {X : Type} (P : list X -> Prop) : Prop :=
  forall xs' x, P xs' -> P (rcons xs' x).

Theorem list_ind_rcons :
  forall {X : Type} (P : list X -> Prop),
    true_for_nil P ->
    preserved_by_rcons P ->
    true_for_list P.
Proof. Admitted.

(*|
But now, I am having trouble using the theorem. I don't how to invoke
it to achieve the same as the ``induction`` tactic.

For example, I tried:
|*)

Require Import List. (* .none *)
Theorem rev_app_dist : forall {X} (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  Fail induction l2 using list_ind_rcons. (* .fails *)

(*| But in the last line, I got: |*)

  Fail induction l2 using list_ind_rcons. (* .unfold .messages *)

(*|
What are the correct steps to define and apply a custom induction
principle like ``list_ind_rcons``?
|*)

(*|
Answer (Anton Trunov)
*********************

If one would like to preserve the intermediate definitions, then one
could use the ``Section`` mechanism, like so:
|*)

Reset Initial. (* .none *)
Require Import Coq.Lists.List. Import ListNotations.

Definition rcons {X : Type} (l : list X) (x : X) : list X :=
  l ++ [x].

Section custom_induction_principle.
  Variable X : Type.
  Variable P : list X -> Prop.

  Hypothesis true_for_nil : P nil.
  Hypothesis true_for_list : forall xs, P xs.
  Hypothesis preserved_by_rcons : forall xs' x, P xs' -> P (rcons xs' x).

  Fixpoint list_ind_rcons (xs : list X) : P xs. Admitted.
End custom_induction_principle.

(*|
Coq substitutes the definitions and ``list_ind_rcons`` has the needed
type and ``induction ... using ...`` works:
|*)

Theorem rev_app_dist : forall {X} (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l2 using list_ind_rcons.
Abort.

(*|
By the way, this induction principle is present in the standard
library (`List <https://coq.inria.fr/library/Coq.Lists.List.html>`__
module):
|*)

Check rev_ind. (* .unfold *)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

What you did was mostly correct. The problem is that Coq has some
trouble recognizing that what you wrote is an induction principle,
because of the intermediate definitions. This, for instance, works
just fine:

.. coq:: none
|*)

Reset Initial.

Definition rcons {X : Type} (l : list X) (x : X) : list X :=
  l ++ x :: nil.

Definition true_for_nil {X : Type} (P : list X -> Prop) : Prop :=
  P nil.

Definition true_for_list {X : Type} (P : list X -> Prop) : Prop :=
  forall xs, P xs.

Definition preserved_by_rcons {X : Type} (P : list X -> Prop) : Prop :=
  forall xs' x, P xs' -> P (rcons xs' x).

Require Import List.

(*||*)

Theorem list_ind_rcons :
  forall {X : Type} (P : list X -> Prop),
    P nil ->
    (forall x l, P l -> P (rcons l x)) ->
    forall l, P l.
Proof. Admitted.

Theorem rev_app_dist : forall {X} (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l2 using @list_ind_rcons.

(*|
I don't know if Coq not being able to automatically unfold the
intermediate definitions should be considered a bug or not, but at
least there is a workaround.

----

**A:** In Coq, there is long standing disrespect for definitional
equality in the implementation of tactics. Whilst this is
questionable, ideologically, it is far too late to do anything about
it in practice.
|*)
