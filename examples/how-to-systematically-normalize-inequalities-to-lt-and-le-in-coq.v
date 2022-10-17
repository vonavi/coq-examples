(*|
##########################################################################################
How to systematically normalize inequalities to ``<`` (``lt``) and ``<=`` (``le``) in Coq?
##########################################################################################

:Link: https://stackoverflow.com/q/34467163
|*)

(*|
Question
********

In proving facts about inequalities (for real numbers), there is
``<``, ``<=``, ``>``, and ``>=``. It's kind of tedious to write down
and use theorems/lemmas for both these forms.

Currently, I am converting these to just ``<`` and ``<=`` manually by
first ``assert`` and then proving a trivial subgoal. I was wondering
if it is possible to automatically normalize all inequalities to just
``<`` and ``<=`` in the hypotheses and the goal?
|*)

(*|
Answer
******

``gt`` and ``ge`` are functions that call ``lt`` and ``le``
respectively on swapped arguments. To get rid of them, just unfold
them.

.. code-block:: coq

    unfold gt, ge.

You may want to unfold ``lt`` as well: it's defined in terms of
``le``. Since the definition of ``gt`` uses ``lt``, unfold ``gt``
first.

.. code-block:: coq

    unfold gt, ge, lt.

You can tell Coq to try this when attempting to prove a goal with
``auto``.

.. code-block:: coq

    Hint Unfold gt ge lt.
|*)
