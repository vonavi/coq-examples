(*|
##########################################
Church numerals and universe inconsistency
##########################################

:Link: https://stackoverflow.com/q/55091525
|*)

(*|
Question
********

In the following code, the statement ``add'_commut`` is accepted by
Coq but ``add_commut is`` rejected because of a universe
inconsistency.
|*)

Set Universe Polymorphism.

Definition nat : Type := forall (X : Type), X -> (X -> X) -> X.

Definition succ (n : nat) : nat := fun X z s => s (n X z s).

Definition add' (m n : nat) : nat := fun X z s => m X (n X z s) s.

Definition nat_rec (z : nat) (s : nat -> nat) (n : nat) : nat := n nat z s.

Definition add (m n : nat) : nat := nat_rec n succ m.

Definition equal (A : Type) (a : A) : A -> Type :=
  fun a' => forall (P : A -> Type), P a -> P a'.

Lemma add'_commut (m n : nat) : equal nat (add' m n) (add' n m).
Admitted.

Fail Lemma add_commut (m n : nat) : equal nat (add m n) (add n m). (* .unfold .fails *)

(*| How to make it go through? |*)

(*|
Answer
******

Church numerals only work if you turn on impredicative ``Set``, by
putting ``-arg -impredicative-set`` into your ``_CoqProject`` file or
using ``-impredicative-set`` command line option. Then define ``nat``
as:
|*)

Fail Definition nat : Set := forall (X : Set), X -> (X -> X) -> X. (* .fails *)

(*|
Impredicative ``Set`` allows ``nat`` to have exactly the same type
``Set`` which it quantifies over. Without impredicativity, ``nat``
must have a higher universe level than what it quantifies over,
although the levels are hidden from you until you get an error like in
the question.

Note that impredicative ``Set`` is `incompatible
<https://github.com/coq/coq/wiki/The-Logic-of-Coq>`__ with classical
logic.
|*)
