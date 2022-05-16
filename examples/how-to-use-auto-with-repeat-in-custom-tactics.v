(*|
######################################################
How to use ``auto`` with ``repeat`` in custom tactics?
######################################################

:Link: https://stackoverflow.com/q/41154060
|*)

(*|
Question
********

In my coq development I am learning how to create new tactics tailored
to my problem domain, a la `Prof. Adam Chlipala
<http://adam.chlipala.net/cpdt/html/Match.html>`__.

On that page he describes how to create powerful tactics by wrapping
``repeat`` around a ``match`` that responds to various interesting
conditions. The ``repeat`` then iterates, allowing for far-reaching
inference.

The use of ``repeat`` has a caveat (emphasis mine):

    The ``repeat`` that we use here is called a *tactical*, or tactic
    combinator. The behavior of ``repeat t`` is to loop through
    running ``t``, running ``t`` on all generated subgoals, running
    ``t`` on *their* generated subgoals, and so on. When ``t`` fails
    at any point in this search tree, that particular subgoal is left
    to be handled by later tactics. **Thus, it is important never to
    use** ``repeat`` **with a tactic that always succeeds.**

Now, I already have a powerful tactic in use, `auto
<https://coq.inria.fr/refman/Reference-Manual010.html#sec390>`__. It
similarly strings together chains of steps, this time found from hint
databases. From ``auto``'s page:

    ``auto`` either solves completely the goal or else leaves it
    intact. ``auto`` **and** ``trivial`` **never fail.**

Boo! I have already invested some effort in curating ``auto``'s hint
databases, but it seems I am forbidden from employing them in tactics
using ``repeat`` (that is, interesting tactics).

Is there some variation of ``auto`` that can fail, or otherwise be
used correctly in loops?

For example, perhaps this variant fails when it "leaves [the goal]
intact".

**EDIT**: Incorporating ``auto`` into loops isn't the "right" way to
do it anyway (see `this
<https://stackoverflow.com/q/41171406/580412>`__), but the actual
question of a failing version of auto is still perhaps interesting.
|*)

(*|
Answer
******

As mentioned by @AntonTrunov you can always use the `progress
<https://coq.inria.fr/refman/proof-engine/ltac.html#coq:tacn.progress>`__
tactical to make the tactic fail if the goal has not been changed. In
the case of `auto
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.auto>`__
since it is supposed to solve the goal or leave it unchanged, you can
also wrap it in ``solve [ auto ]`` which will have the same effect
because it will fail if ``auto`` does not solve the goal completely
(`here is the doc for solve
<https://coq.inria.fr/refman/proof-engine/ltac.html#coq:tacn.solve>`__).
|*)
