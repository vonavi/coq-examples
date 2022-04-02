(*|
################################################
Interaction between type classes and auto tactic
################################################

:Link: https://stackoverflow.com/q/46244909
|*)

(*|
Question
********

Consider this simple development. I have two trivial data types:
|*)

Inductive A :=
| A1
| A2.

Inductive B :=
| B1 : A -> B
| B2.

(*|
Now I introduce a concept of relation and define ordering on data
types ``A`` and ``B`` expressed as an inductive data type:
|*)

Definition relation (X : Type) := X -> X -> Prop.

Reserved Notation "a1 '<=A' a2" (at level 70).

Inductive AOrd : relation A :=
| A1_Ord : A1 <=A A1
| A2_Ord : A2 <=A A2
| A1_A2  : A1 <=A A2
where "a1 '<=A' a2" := (AOrd a1 a2).

Reserved Notation "b1 '<=B' b2" (at level 70).

Inductive BOrd : relation B :=
| B1_Ord : forall a1 a2,
    a1 <=A a2 -> B1 a1 <=B B1 a2
| B2_Ord :
  B2 <=B B2
| B1_B2  : forall a,
    B1 a <=B B2
where "b1 '<=B' b2" := (BOrd b1 b2).

(*|
Finally, I introduce a concept of reflexivity and prove that both of
my relations are reflexive:
|*)

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Hint Constructors AOrd BOrd.

Theorem AOrd_reflexive : reflexive AOrd.
Proof.
  intro a. induction a; auto.
Qed.

Hint Resolve AOrd_reflexive.

Theorem BOrd_reflexive : reflexive BOrd.
Proof.
  intro b. induction b; auto.
Qed.

(*|
Both proofs are finished with ``auto`` tactic, with the first proof
crucially relying on ``Hint Constructors`` and the second one
additionally on ``Hint Resolve AOrd_reflexive being`` added to hint
database.

An ugly thing about the code above is having a separate notation for
ordering relation for ``A`` and ``B`` data types. I'd like to be able
to uniformly use ``<=`` everywhere. `This answer
<https://stackoverflow.com/a/44057494/1273482>`__ provides a solution
to the problem: use type classes. So I introduce a type class for
ordering and redefine my ordering relations to use this new notation:
|*)

Reset AOrd. (* .none *)
Class OrderR (T : Type) := orderR : relation T.
Notation "x '<=' y" := (orderR x y) (at level 70).

Inductive AOrd : OrderR A :=
| A1_Ord : A1 <= A1
| A2_Ord : A2 <= A2
| A1_A2  : A1 <= A2.

Inductive BOrd `{OrderR A} : OrderR B :=
| B1_Ord : forall a1 a2,
    a1 <= a2 -> B1 a1 <= B1 a2
| B2_Ord :
  B2 <= B2
| B1_B2  : forall a,
    B1 a <= B2.

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a. (* .none *)
Hint Constructors AOrd BOrd.

(*| But now proof automation breaks! For example: |*)

Theorem AOrd_reflexive : reflexive AOrd.
Proof.
  intro a. induction a.

(*| leaves me with a goal: |*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
that ``auto`` no longer solves despite ``AOrd`` constructors being in
hint database. I can solve the goal with ``constructor`` though:
|*)

Theorem AOrd_reflexive : reflexive AOrd.
Proof.
  intro a. induction a; constructor.
Qed.

(*| More problems arise in second proof. After doing: |*)

Theorem BOrd_reflexive `{OrderR A} : reflexive BOrd.
Proof.
  intro b. induction b; constructor.

(*| I am left with goal: |*)

  Show. (* .unfold .messages *)

(*|
Again, ``auto`` no longer solves this goal. Even ``apply
AOrd_reflexive`` does not work.

My question is: is it possible to have a uniform notation by relying
on type classes and maintain benefits of proof automation? Or is there
a different solution to having a uniform notation for various data
types.
|*)

(*|
Answer (eponier)
****************

A solution that does not involve typeclasses is to take advantage of
the scope mechanism of Coq.
|*)

Reset Initial. (* .none *)
Inductive A :=
| A1
| A2.

Inductive B :=
| B1 : A -> B
| B2.

Definition relation (X : Type) := X -> X -> Prop.

Reserved Notation "a1 '<=' a2" (at level 70).

Inductive AOrd : relation A :=
| A1_Ord : A1 <= A1
| A2_Ord : A2 <= A2
| A1_A2  : A1 <= A2
where "a1 '<=' a2" := (AOrd a1 a2) : a_scope.

Delimit Scope a_scope with a.

Inductive BOrd : relation B :=
| B1_Ord : forall a1 a2,
    (a1 <= a2)%a -> B1 a1 <= B1 a2
| B2_Ord :
  B2 <= B2
| B1_B2  : forall a,
    B1 a <= B2
where "b1 '<=' b2" := (BOrd b1 b2) : b_scope.

Delimit Scope b_scope with b.

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Hint Constructors AOrd BOrd.

Theorem AOrd_reflexive : reflexive AOrd.
Proof.
  intro a. induction a; auto.
Qed.

Hint Resolve AOrd_reflexive.

Theorem BOrd_reflexive : reflexive BOrd.
Proof.
  intro b. induction b; auto.
Qed.

(*|
Answer (Jason Gross)
********************

The issue is that your hints are set to trigger on, e.g., ``@orderR _
AOrd A1 A2``, not ``AOrd A1 A2``. So the automation never sees the
pattern it's looking for, and never triggers the hints. Here are two
solutions:

1. You can adjust the type of your constructors when adding them to
   the hint database, so that they trigger when you want them to:

   .. coq:: none
|*)

Reset AOrd.
Class OrderR (T : Type) := orderR : relation T.
Notation "x '<=' y" := (orderR x y) (at level 70).

Inductive AOrd : OrderR A :=
| A1_Ord : A1 <= A1
| A2_Ord : A2 <= A2
| A1_A2  : A1 <= A2.

Inductive BOrd `{OrderR A} : OrderR B :=
| B1_Ord : forall a1 a2,
    a1 <= a2 -> B1 a1 <= B1 a2
| B2_Ord :
  B2 <= B2
| B1_B2  : forall a,
    B1 a <= B2.

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Hint Constructors AOrd BOrd.

(*||*)

Hint Resolve (A1_Ord : AOrd _ _) (A2_Ord : AOrd _ _) (A1_A2 : AOrd _ _).
Hint Resolve (@B1_Ord : forall H a1 a2, _ -> BOrd _ _)
     (@B2_Ord : forall H, BOrd _ _)
     (@B1_B2 : forall H a, BOrd _ _).

(*|
2. You can define "folding" lemmas that convert the types, and add
   those to the database:
|*)

Definition fold_AOrd a1 a2 (v : a1 <= a2) : AOrd a1 a2 := v.
Definition fold_BOrd `{OrderR A} (a1 a2 : B) (v : a1 <= a2) : BOrd a1 a2 := v.
Hint Resolve fold_AOrd fold_BOrd.

(*|
----

**Q:** Thanks Jason. I'm afraid your solution does not work for me.
Folding lemmas don't seem to change anything. Adjusting type of
constructors works when proving ``AOrd_reflexive`` but in the proof of
``BOrd_reflexive`` it is still not possible to prove ``a <= a`` from
``AOrd_reflexive``.
|*)
