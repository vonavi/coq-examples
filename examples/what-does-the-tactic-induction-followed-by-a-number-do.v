(*|
###########################################################
What does the tactic ``induction`` followed by a number do?
###########################################################

:Link: https://stackoverflow.com/q/55766757
|*)

(*|
Question
********

What effect does the following tactic have on the goal and the
assumptions? I know what induction on variables and named hypothesis
do, but am unclear about induction on a number.

.. code-block:: coq

    Induction 1
|*)

(*|
Answer
******

From the Coq Reference Manual:
https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#coq:tacn.induction

    (...) ``induction num`` behaves as ``intros until num`` followed
    by ``induction`` applied to the last introduced hypothesis.

And for ``intros until num``:
https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#coq:tacv.intros

    ``intros until num``: This repeats intro until the ``num``-th
    non-dependent product.

    **Example**

    On the subgoal ``forall x y : nat, x = y -> y = x`` the tactic
    ``intros until 1`` is equivalent to ``intros x y H``, as ``x = y
    -> y = x`` is the first non-dependent product.

    On the subgoal ``forall x y z : nat, x = y -> y = x`` the tactic
    ``intros until 1`` is equivalent to ``intros x y z`` as the
    product on ``z`` can be rewritten as a non-dependent product:
    ``forall x y : nat, nat -> x = y -> y = x``.

For reference, there is an index of standard tactics in the Manual
where those can easily be looked up:
https://coq.inria.fr/distrib/current/refman/coq-tacindex.html

(There are other indices in there that you may find interesting as
well.)

----

**Q:** So in your first example, ``forall x y : nat, x = y -> y = x``.
``Induction 1`` applies induction to ``x = y``? What does a
non-dependent product mean exactly? Form your examples, it seems to
refer to a quantifier-free formula...

**A:** Yes, that's induction on ``x = y``. "Product" here refers to
function types: ``forall x, F x`` has similarities to ``Π x, F x``
(product over all ``x`` of ``F x``), and in fact ``Π`` is used instead
of ``forall`` in some areas in the literature. When ``F x`` is
actually a constant ``C``, ``forall x : T, C`` is called a
non-dependent product.
|*)
