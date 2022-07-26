(*|
################################################
Coq ``Qed`` raise a warning with admitted lemmas
################################################

:Link: https://stackoverflow.com/q/71938137
|*)

(*|
Question
********

When developing a big system in Coq, I usually admit many lemmas and
see whether the important theorem works or not, and then solve lemmas
one by one.

Coq accepts ``Qed.`` even with admitted lemmas, so sometimes I'm not
100% sure whether I solve all the admits and need to seek help with
text search ``admit`` and ``Admitted``, is there a more strict version
of ``Qed.`` which doesn't allow theorems to be proved with admitted
lemmas?

.. code-block:: coq

    Print Assumptions lemma_names.

seems a feasible way to check, are there other solutions?

----

**A:** ``Print Assumptions`` on the main theorem is indeed the
standard way to go. Also when it's your own admits that you want to
check, looking for ``Admitted`` should suffice.
|*)
