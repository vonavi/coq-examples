(*|
#######################################################################
In Coq, which tactic to change the goal from ``S x = S y`` to ``x = y``
#######################################################################

:Link: https://stackoverflow.com/q/13749403
|*)

(*|
Question
********

I want to change the goal from ``S x = S y`` to ``x = y``. It's like
``inversion``, but for the goal instead of a hypothesis.

Such a tactic seems legit, because when we have ``x = y``, we can
simply use ``rewrite`` and ``reflexivity`` to prove the goal.

Currently I always find myself using ``assert (x = y)`` to introduce a
new subgoal, but it's tedious to write when ``x`` and ``y`` are
complex expression.
|*)

(*|
Answer
******

The tactic ``apply f_equal.`` will do what you want, for any
constructor or function.

The lema ``f_equal`` shows that for any function ``f``, you always
have ``x = y -> f x = f y``. This allows you to reduce the goal from
``f x = f y`` to ``x = y``:
|*)

Proposition myprop (x y : nat) (H : x = y) : S x = S y.
Proof.
  apply f_equal. assumption.
Qed.

(*|
(The ``injection`` tactic implements the converse implication --- that
for some functions, and in particular for constructors, ``f x = f y ->
x = y``.)

----

**A:** You can also use the ``f_equal`` tactic, which saves some
typing.
|*)
