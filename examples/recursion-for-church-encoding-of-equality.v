(*|
#########################################
Recursion for Church encoding of equality
#########################################

:Link: https://stackoverflow.com/questions/55089210/recursion-for-church-encoding-of-equality
|*)

(*|
Question
********

For the Church encoding ``N`` of positive integers, one can define a
recursion principle ``nat_rec``:
|*)

Definition N : Type := forall (X : Type), X -> (X -> X) -> X.

Fail Definition nat_rec (z : N) (s : N -> N) (n : N) : N :=
  n N z s. (* .fails *)

(*|
What is the recursion principle ``equal_rec`` for the following Church
encoding ``equal`` of equality?
|*)

Variable A : Type. (* .none *)
Definition equal (x : A) : A -> Type :=
  fun x' => forall (P : A -> Type), P x -> P x'.

(*|
.. code-block:: coq

    Definition equal_rec (* ... *)
|*)

(*|
Answer
******

Like the case of natural numbers, the recursion principle is simply an
eta expansion:
|*)

Reset equal. (* .none *)
Definition equal {A : Type} (x : A) : A -> Type :=
  fun x' => forall (P : A -> Type), P x -> P x'.

Definition equal_rec (A : Type) (x y : A) (e : equal x y) (P : A -> Type) :
  P x -> P y := e P.

(*|
----

**Q:** This looks pretty useless, isn't it? Can it be used to prove
symmetry, transitivity or congruence of equality?

**A:** It cannot, because of universe issues. But you can replace
``Type`` by ``Prop`` everywhere, and it should work.
|*)
