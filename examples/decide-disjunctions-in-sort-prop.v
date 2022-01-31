(*|
####################################
Decide disjunctions in sort ``Prop``
####################################

:Link: https://stackoverflow.com/q/55952695
|*)

(*|
Question
********

I am interested in the probably false lemma:
|*)

Lemma decideOr : forall (P Q : Prop),
    (P \/ Q) -> {P} + {Q}.
Abort. (* .none *)

(*|
that asserts we can algorithmically decide any proof of an ``or`` in
sort ``Prop``. Of course, Coq does not let us ``destruct`` the input
to extract it in sort ``Set``. However, a proof of ``P \/ Q`` is a
lambda-term that Coq accepts to print, so external tools can process
it.

First question: can this lambda-term be decided outside of Coq
(assuming the term uses no axioms, only plain Coq)? It might be,
because the rules of constructive logic demand that all disjunctions
be explicitely chosen, without cheating by a proof by contradiction.
So can we code a parser of Coq proof terms, and try to decide whether
the first or the second operand of the ``or`` was proved? If the term
starts with ``or_introl`` or ``or_intror`` we are done. So I guess the
problems are when the term is a lambda-application. But then Coq terms
are strongly normalizing, so we reduce it to a normal form and it
seems it will start with either ``or_introl`` or ``or_intror``.

Second question: if this problem can be decided outside of Coq, what
prevents us from internalizing it within Coq, ie proving lemma
``decideOr`` above?
|*)

(*|
Answer
******

First question
==============

Yes, you can write a program that takes as input a Coq proof of ``A \/
B`` and outputs ``true`` or ``false`` depending on which side was used
to prove the disjunction. Indeed, if you write

.. code-block:: coq

    Compute P.

in Coq, where ``P : A \/ B``, Coq will normalize the proof ``P`` and
print which constructor was used. This will not work if ``P`` uses
proofs that end in ``Qed`` (because those are not unfolded by the
evaluator), but in principle it is possible to replace ``Qed`` by
``Defined`` everywhere and make it work.

Second question
===============

What prevents us from proving ``decideOr`` is that the designers of
Coq wanted to have a type of propositions that supports the excluded
middle (using an axiom) while allowing programs to execute. If
``decideOr`` were a theorem *and* we wanted to use the excluded middle
(``classical : forall A : Prop, A \/ ~ A``), it would not be possible
to execute programs that branch on the result of ``decideOr (classical
A)``. This does not mean that ``decideOr`` is false: it is perfectly
possible to admit it as an axiom. There is a difference between not
being provable ("there does not exist a proof of ``A``") and being
refutable ("there exists a proof of ``~ A``").
|*)
