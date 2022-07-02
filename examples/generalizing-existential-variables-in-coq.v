(*|
#########################################
Generalizing existential variables in Coq
#########################################

:Link: https://stackoverflow.com/q/12199271
|*)

(*|
Question
********

I'm trying to prove ``P ?x``, where ``P : A -> Prop`` and ``?x : A``
is an existential variable. I can prove ``forall a : A, P a``, so I
need to generalize ``P ?x`` to ``forall a : A, P a``.

If ?x was an instantiated variable, x, I could simply use ``generalize
x`` to produce ``forall x : A, P x``. When I try ``generalize ?x``,
however, Coq returns a syntax error.

Is this possible? I've checked and Coq does not seem to provide an
intuitive way to generalize statements about existential variables.
|*)

(*|
Answer
******

``P ?x`` is not equivalent to ``forall x, P x``, nor even implied by
it. To prove ``P ?x``, you need to find some ``a`` such that ``P a``
holds. With your hypothesis, it suffices to find some ``a : A``. In
other words, you need to prove that the domain is not empty (or more
precisely, you need to prove the existence of an element in the
domain).

Here, if you have some ``a : A``, you can use ``instantiate (1 :=
A)``. Silly example:
|*)

Parameter A : Set.
Parameter P : A -> Prop.
Goal (forall a, P a) -> A -> exists x, P x.
Proof.
  intros H a. eexists. instantiate (1 := a). apply H.
Qed.
