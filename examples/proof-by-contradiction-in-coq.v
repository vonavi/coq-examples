(*|
#############################
Proof by contradiction in Coq
#############################

:Link: https://stackoverflow.com/q/71945260
|*)

(*|
Question
********

I am trying to understand the apparent paradox of the logical
framework of theorem provers like Coq not including LEM yet also being
able to construct proofs by contradiction. Specifically the
intuitionistic type theory that these theorem provers are based on
does not allow for any logical construction of the form ``￢(￢P)⇒P``,
and so what is required in order to artificially construct this in a
language like Coq? And how is the constructive character of the system
preserved if this is allowed?
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

I think you are mixing up two related uses of contradiction in logic.
One is the technique of *proof by contradiction*, which says that you
can prove ``P`` by proving ``~ (~ P)`` -- that is, by showing that ``~
P`` entails a contradiction. This technique is actually *not*
available in general in constructive logics like Coq, unless one of
the following applies.

1. You add the excluded middle ``forall P, P \/ ~ P`` as an axiom. Coq
   supports this, but this addition means that you are not working in
   a constructive logic anymore.
2. The proposition ``P`` is known to be decidable (i.e., ``P \/ ~ P``
   holds). This is the case, for example, for the equality of two
   natural numbers ``n`` and ``m``, which we can prove by induction.
3. The proposition ``P`` is of the form ``~ Q``. Since ``Q -> ~ (~
   Q)`` holds constructively, by the law of contrapositives (which is
   also valid constructively), we obtain ``~ (~ (~ Q)) -> (~ Q)``.

The other use of contradiction is the `principle of explosion
<https://en.wikipedia.org/wiki/Principle_of_explosion>`__, which says
that anything follows once you assume a contradiction (i.e., ``False``
in Coq). Unlike proof by contradiction, the principle of explosion is
*always* valid in constructive logic, so there is no paradox here.
|*)

(*|
Answer (L. Garde)
*****************

In constructive logic, by definition, a contradiction is an inhabitant
of the empty type ``0``, and, also by definition, the negation ``￢P``
of a proposition ``P`` is a function of type: ``P -> 0`` that gives an
inhabitant of the empty type ``0`` from an inhabitant (a proof) of
``P``.

If you assume an inhabitant (proof) of ``P``, and derive
constructively an inhabitant of ``0``, you have defined a function
inhabiting the type ``P -> 0``, i.e. a proof of ``￢P``. This is a
constructive sort of proof by contradiction: assume ``P``, derive a
contradiction, conclude ``￢P``.

Now if you assume ``￢P`` and derive a contradiction, you have a
constructive proof of ``￢￢P``, but cannot conclude constructively
that you have a proof of ``P``: for this you need the LEM axiom.
|*)
