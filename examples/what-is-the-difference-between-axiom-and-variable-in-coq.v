(*|
################################################################
What is the difference between ``Axiom`` and ``Variable`` in Coq
################################################################

:Link: https://stackoverflow.com/q/61344787
|*)

(*|
Question
********

In Coq I can write
|*)

Variable A : False.
Axiom B : False.

(*|
which assume ``False`` under names ``A`` and ``B``. Both statements
work in proofs, so I can
|*)

Theorem nothing_makes_sense : forall (a : Type), a.
  destruct true; exfalso.
  * apply A.
  * apply B.
Qed.

(*|
What is the actual difference? When should I use one instead of
another?
|*)

(*|
Answer
******

It is advised to use the commands Axiom, Conjecture and Hypothesis
(and their plural forms) for logical postulates (i.e. when the
assertion type is of sort Prop), and to use the commands Parameter and
Variable (and their plural forms) in other cases (corresponding to the
declaration of an abstract mathematical entity).

And as you can see in the specification of coq
https://coq.inria.fr/refman/coq-cmdindex.html they are defined in the
same way.
|*)
