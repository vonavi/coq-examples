(*|
###################################
Using an existential theorem in Coq
###################################

:Link: https://stackoverflow.com/q/12214778
|*)

(*|
Question
********

I have the following theorem in Coq: ``Theorem T : exists x : A, P
x.`` I want to be able to use this value in a subsequent proof. I.E. I
want to say something like: "let ``o`` represent a value such that ``P
o``. I know that ``o`` exists by theorem ``T``..."
|*)

(*|
Answer
******

Mathematically speaking, you need to apply an elimination rule for the
∃ constructor. The generic elimination tactic ``elim`` works.

.. code-block:: coq

    elim T; intro o.

Silly example:
|*)

Parameter A : Prop.
Parameter P : A -> Prop.
Axiom T : exists x : A, P x.
Parameter G : Prop.
Axiom U : forall x : A, P x -> G.
Goal G.
Proof.
  elim T; intro o.
  apply U.
Qed.
