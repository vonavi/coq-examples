(*|
#####################################################
Multiple successes in Coq branching and backtracking?
#####################################################

:Link: https://stackoverflow.com/q/38256705
|*)

(*|
Question
********

I am having trouble understanding the concept of ``multiple
successes`` in Coq's (8.5p1, ch9.2) branching and backtracking
behavior. For example, from the documentation:

    **Backtracking branching**

    We can branch with the following structure:

    .. code-block::

        expr1 + expr2

    Tactics can be seen as having several successes. When a tactic
    fails it asks for more successes of the prior tactics. ``expr1 +
    expr2`` has all the successes of ``v1`` followed by all the
    successes of ``v2``.

What I don't understand, is why do we need multiple successes in the
first place? Isn't one success good enough to finish a proof?

Also from the documentation, it seems that there are less costly
branching rules that are somehow "biased", including

.. code-block:: coq

    first [ expr1 | ::: | exprn ]

and

.. code-block:: coq

    expr1 || expr2

Why do we need the more costly option ``+`` and not always use the
latter, more efficient tacticals?
|*)

(*|
Answer
******

The problem is that you are sometimes trying to discharge a goal but
further subgoals might lead to a solution you thought would work to be
rejected. If you accumulate all the successes then you can backtrack
to wherever you made a wrong choice and explore another branch of the
search tree.

Here is a silly example. let's say I want to prove this goal:
|*)

Goal exists m, m = 1.
Abort. (* .none *)

(*|
Now, it's a fairly simple goal so I could do it manually but let's
not. Let's write a tactic that, when confronted with an ``exists``,
tries all the possible natural numbers. If I write:
|*)

Ltac existNatFrom n :=
  exists n || existNatFrom (S n).

Ltac existNat := existNatFrom O.

(*|
then as soon as I have run ``existNat``, the system commits to the
first successful choice. In particular this means that despite the
recursive definition of ``existNatFrom``, when calling ``existNat``
I'll always get ``O`` and only ``O``.

The goal cannot be solved:
|*)

Goal exists m, m = 1.
  Fail (existNat; reflexivity).
Abort.

(*|
On the other hand, if I use ``(+)`` instead of ``(||)``, I'll go
through all possible natural numbers (in a lazy manner, by using
backtracking). So writing:
|*)

Ltac existNatFrom' n :=
  exists n + existNatFrom' (S n).

Ltac existNat' := existNatFrom' O.

(*| means that I can now prove the goal: |*)

Goal exists m, m = 1.
  existNat'; reflexivity.
Qed.
