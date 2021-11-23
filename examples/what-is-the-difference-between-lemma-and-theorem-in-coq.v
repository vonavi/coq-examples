(*|
What is the difference between Lemma and Theorem in Coq
=======================================================

:Link: https://stackoverflow.com/questions/56517779/what-is-the-difference-between-lemma-and-theorem-in-coq
|*)

(*|
Question
--------

I can't tell in which situations I should use ``Theorem`` over
``Lemma`` or the opposite. Is there any difference (despite
syntactical) between this
|*)

Theorem l : 2 = 2.
  trivial.
Qed.

(*| and this |*)

Reset l. (* .none *)
Lemma l : 2 = 2.
  trivial.
Qed.

(*| ? |*)

(*|
Answer
------

There is no difference between ``Theorem`` and ``Lemma`` as far as the
language is concerned. The reasons to choose one over another are
purely psychological. You can also use ``Remark``, ``Fact``,
``Corollary``, ``Proposition`` according to the importance you
attribute to the result. Here is the `relevant link
<https://coq.inria.fr/refman/language/gallina-specification-language.html#coq:cmd.theorem>`_
in the Coq reference manual.

Some projects' code style guides only allow one keyword to be used for
uniformity. This might help reading source code and allow using simple
grep-like tools to extract some statistics from it.
|*)
