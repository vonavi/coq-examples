(*|
################################################################
Coq: easiest way to construct members of a decidable sigma type?
################################################################

:Link: https://stackoverflow.com/q/71595304
|*)

(*|
Question
********

Consider the following toy development:
|*)

Inductive IsEven : nat -> Prop :=
| is_even_z : IsEven 0
| is_even_S : forall n, IsEven n -> IsEven (S (S n)).

Definition EvenNat := {n | IsEven n}.

(*|
I'd like to create a function that, given a number that I personally
know to be even, returns the corresponding value of type ``EvenNat``
with minimum fuss.

.. code-block:: coq

    Example fortyTwo : EvenNat := mkEven 42.
|*)

(*|
Answer (Théo Winterhalter)
**************************

I don't know exactly what your assumptions are but I would say one way
of doing it is to use the automation capabilities of type classes:
|*)

Reset Initial. (* .none *)
Require Import Coq.Init.Specif.

Inductive IsEven : nat -> Prop :=
| is_even_z : IsEven 0
| is_even_S : forall n, IsEven n -> IsEven (S (S n)).

Class EvenClass n :=
  is_even : IsEven n.

Definition EvenNat := { n | EvenClass n }.

Lemma EvenClass_IsEven :
  forall n, EvenClass n -> IsEven n.
Proof.
  intros n h. exact h.
Qed.

#[export] Hint Extern 1 (EvenClass 0) =>
  apply is_even_z
  : typeclass_instances.

#[export] Hint Extern 1 (EvenClass (S (S ?n))) =>
  apply is_even_S; apply EvenClass_IsEven
    : typeclass_instances.

#[export] Hint Extern 1 (EvenClass (proj1_sig ?x)) =>
  apply proj2_sig
  : typeclass_instances.

Ltac my_decision_procedure := id. (* .none *)
#[export] Hint Extern 4 (EvenClass ?n) =>
  my_decision_procedure
  : typeclass_instances.

(*|
Instead of defining instances, I use the ``Hint Extern`` mechanism to
inject any tactic I want to solve the goal. Assuming you have a tactic
to decide your property you can use it there. The natural number
indicates the "cost" to each hint so the search will try to apply the
hints with the lowest costs first.

Once you have this, the function you want is
|*)

Definition mkEven (n : nat) {h : EvenClass n} : EvenNat :=
  exist _ n h.

(*|
Then just writing ``mkEven n`` will trigger the proof search as
described by the hints above.
|*)

Definition ev := mkEven 42.

(*|
----

To elaborate the difference between Yves's and my answer, I chose to
use hints rather than class instances so that the proof search is not
too greedy.

For instance, I force the search to only use ``is_even_z`` when I
really want to prove ``EvenClass 0``, as exemplified by the example
below:
|*)

Goal exists n, EvenClass n.
Proof.
  eexists. Fail exact _.
Abort.

Instance foo : EvenClass 0.
Proof.
  exact _.
Qed.

Goal exists n, EvenClass n.
Proof.
  eexists. exact _.
Qed.

(*|
As you can see, in the first case, we have ``EvenClass ?n`` as a goal,
and so the proof search does not find any candidate. However, if we
add the ``0`` case as a type class instance, then the proof search
will succeed by unifying ``?n`` with ``0``. It is my belief that this
is doing a bit too much for the case at hand here, but both solutions
have their applications.
|*)

(*|
Answer (Yves)
*************

The question, as originally stated, has an obvious answer.

*Question A*: If you have in your context a number ``n`` of type
``nat`` and a proof ``knowledge`` with statement ``IsEven n``, how do
you construct an object of type ``EvenNat``?

you can simply construct an object of type ``EvenNat`` by writing the
following expression

.. code-block:: coq

    exist _ n knowledge

Or, if you really want to be explicit:

.. code-block:: coq

    exist IsEven n knowledge

This is embodied in the following script
|*)

Reset Initial. (* .none *)
Inductive IsEven : nat -> Prop :=
| is_even_z : IsEven 0
| is_even_S : forall n, IsEven n -> IsEven (S (S n)).

Definition EvenNat := {n | IsEven n}.

Definition mkEven (n : nat) (knowledge : IsEven n) : EvenNat :=
  exist IsEven n knowledge.

(*|
Another reading of the question is as follows:

*Question B*: how do you construct an object of type ``EvenNat`` from
a known constant (like ``42``) which is obviously even to the naked
eye?

Here is my elaboration of a solution sketched by Theo Winterhalter,
using the device of type classes in full.
|*)

Reset Initial. (* .none *)
Require Import Coq.Init.Specif.

Inductive IsEven : nat -> Prop :=
| is_even_z : IsEven 0
| is_even_S : forall n, IsEven n -> IsEven (S (S n)).

Definition EvenNat := {n | IsEven n}.

Definition makeEvenNat (n : nat) (knowledge : IsEven n) : EvenNat :=
  exist IsEven n knowledge.

Class EvenClass n : Prop :=
  is_even : IsEven n.

Instance evenClass0 : EvenClass 0.
Proof.
  apply is_even_z.
Qed.

Instance evenClassS n {h : EvenClass n}  : EvenClass (S (S n)).
Proof.
  apply is_even_S. exact h.
Qed.

(* Using curly braces for the second argument h here deserves an
  explanation. *)
Definition mkEven (n : nat) {h : EvenClass n} : EvenNat :=
  exist IsEven n h.

Definition ev42 := mkEven 42.

Lemma ev42P : proj1_sig ev42 = 42.
Proof. easy. Qed.

Lemma IsEven42 : IsEven 42.
Proof. exact (proj2_sig ev42). Qed.

(*|
The explanation for using curly braces in the definition of ``mkEven``
is that ``mkEven`` actually requires 2 arguments, but the second one
is not written by the user: it must be automatically constructed using
the type class inference mechanism. This proof must succeed for the
object to be actually defined.

The definition of ``ev42`` is the answer of question *B*. Note that a
definition relying on ``mkEven 3`` will fail, because no proof that
``3`` is even can be found.
|*)

Fail Definition ev3 := mkEven 3.
