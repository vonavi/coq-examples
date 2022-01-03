(*|
####################################################################
How to step through semicolons separated tactics sequence in coqide?
####################################################################

:Link: https://stackoverflow.com/q/58021053
|*)

(*|
Question
********

when constructing proof in coqide, I didn't find a way to step though

.. code-block:: coq

    T1; T2; T3; ...; Tn.

one tactic by one tactic. So it became very difficult to **construct**
correct proof like the code above. So my question is

- Is there a way to step through the code above or
- How do you construct proof like the code above?

Forward one Command or go to cursor aren't work.
|*)

(*|
Answer
******

``t1; t2`` is not the same as doing first ``t1`` then ``t2``. If you
want to do this you can do ``t1. t2.`` and this is the way to step
through them.

The semicolon serves three purposes, stated for ``t1; t2``:

- It applies ``t2`` in all of the subgoals generated by ``t1``;
- and it allows backtracking, if ``t2`` were to fail, it would try a
  different *success* for ``t1`` and apply ``t2`` again on the
  generated subgoals;
- third, it's the simplest way to write down a tactic that represents
  a succession of tactics.

If you're lucky and this is the first or third case, then you can
modify the script by replacing

.. code-block:: coq

    t1; t2

by

.. code-block:: coq

    t1. all: t2.

using goal selectors. This way the first step will allow you to see
the goals generated by ``t1`` and the second will show you how ``t2``
affects them. If you need more precision you can also focus one of the
subgoals to see ``t2`` in action.

When backtracking is involved it becomes much harder to understand
what is going on, but I believe it can be avoided at first, or limited
to simple cases. You could for instance say that the goal can be
closed by applying an introduction rule (``constructor``) and that
then it should be easy. If multiple intro-rules/constructors apply
doing

.. code-block:: coq

    constructor. easy.

might result in failure, while

.. code-block:: coq

    constructor; easy.

might succeed. Indeed, if ``easy`` fails on the first constructor, coq
will try the second and so on.

To answer your question about how one would write them, I suppose it
can be the result of trial and error, and can mostly stem from
factorisation or automation of proof scripts. Say you have the
following proof script:

.. code-block:: coq

    split.
    - constructor.
      + assumption.
      + eassumption.
    - constructor. eassumption.

You might want to summarise it as follows:

.. code-block:: coq

    split; constructor; eassumption.

I personally don't necessarily recommend it because it becomes harder
to maintain and harder to read for other users because of the issue of
not being able to step through. I would limit this to cases where the
proof is principled (like applying a constructor and be done with it),
and resort to goal selectors for factorisation.
|*)
