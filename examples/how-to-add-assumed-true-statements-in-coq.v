(*|
###########################################
How to add "assumed true" statements in Coq
###########################################

:Link: https://stackoverflow.com/q/68060895
|*)

(*|
Question
********

I tried to add a definition of a natural number in CoqIDE.
|*)

Inductive nat : Set :=
| O: nat
| S: nat -> nat.

(*|
But I couldn't add this as "assumed true":

.. code-block:: coq

    forall (n m: nat, S n = S m -> n = m).

How do I add this?
|*)

(*|
Answer
******

I'm not completely clear on what you want to do, but your formula is
not syntactically correct. I believe you meant ``forall (n m: nat), S
n = S m -> n = m`` (note the parenthesis' placement).

Your statement is actually provable, no need to assume it:
|*)

Lemma S_inj : forall (n m: nat), S n = S m -> n = m.
Proof. intros n m [=]. assumption. Qed.

(*|
The ``[=]`` `intro pattern
<https://coq.inria.fr/refman/proof-engine/tactics.html#intropattern-inj-discr-ex>`__
expresses the built-in injectivity of the ``S`` constructor.
|*)
