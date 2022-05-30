(*|
######################################################
Injectivity of ``inl`` and ``inr`` in standard library
######################################################

:Link: https://stackoverflow.com/q/32503986
|*)

(*|
Question
********

Where in the Coq standard library can I find a lemma stating that
``inl`` and ``inr`` are injections? That is,
|*)

Goal forall (A B : Type) (x y : A), inl B x = inl B y -> x = y.

(*|
and analogously for the right-hand case. I don't have a problem
proving this by myself, but these seem like such useful and important
lemmas to have that I have to imagine they are already in the standard
library somewhere.
|*)

(*|
Answer
******

Since all constructors of inductive types are injective, it would be
quite a hassle to define all those lemmas. Arguably, they could be
defined automatically the way the induction principles are defined,
but, they can be derived from them.

Anyway, if your need for the lemma is to make profress in a different
proof, you should know about the tactic `injection
<https://coq.inria.fr/distrib/current/refman/Reference-Manual010.html#hevea_tactic84>`__,
which retrieves all the necessary equalities for you.
|*)
