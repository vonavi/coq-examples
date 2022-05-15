(*|
############################################################
Multiple ``where``-clauses for ``Reserved Notation`` in Coq?
############################################################

:Link: https://stackoverflow.com/q/42282579
|*)

(*|
Question
********

I've got a bunch of mutually-inductive datatypes declared using
``with``, and I'd like to define a ``Notation`` for each of them that
I can use while I'm defining them.

I'm aware of `Reserved Notations
<https://coq.inria.fr/refman/Reference-Manual014.html>`__ and ``with``
clauses, but I can't figure out the syntax to define multiple
notations which are avaliable to all of my mutually-inductive types.

Is it possible to define multiple Notations in ``where``-clauses, and
if so, does anyone have an example of this I can see?
|*)

(*|
Answer
******

An example:
|*)

Reserved Notation "# n" (at level 80).
Reserved Notation "! n" (at level 80).

Inductive even : nat -> Set :=
| ev0 : #0
| evS : forall n, !n -> # S n
where "# n" := (even n)
with odd : nat -> Set :=
  odS : forall n, #n -> ! S n
where "! n" := (odd n).
