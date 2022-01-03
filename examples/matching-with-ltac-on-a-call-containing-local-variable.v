(*|
######################################################
Matching with Ltac on a call containing local variable
######################################################

:Link: https://stackoverflow.com/q/48568716
|*)

(*|
Question
********

I have a goal that contains a call to some lemma ``foo`` within branch
of a match. That call uses as one of its arguments a variable ``R``
local to the branch:

.. code-block:: coq

    | SomeConstr => fun R => ... (foo a b c R) ...

I would like to perform beta expansion on ``foo`` so that the call
becomes:

.. code-block:: coq

    | SomeConstr => fun R => ... ((fun d => foo a b c d) R) ...

This will allow me to further generalize ``(fun d => foo a b c d)``,
which will no loner rely on variables local to a branch. Since I am
dealing with very large proofs I would like to write this using Ltac.
Here's an attempt:

.. code-block:: coq

    match goal with
    | [ |- context[(foo ?A ?B ?C ?R)] ] =>
      let d := fresh "d" in
      replace (foo A B C R) with ((fun d => foo A B C d) R)
    end.

That however fails with "No matching clause for match". If I replace
body of the ``match`` branch with ``idtac`` it still fails, so the
problem is clearly cause by failing to match a given expression.
However, if I match one argument less then the match succeeds. For
example:

.. code-block:: coq

    match goal with
    | [ |- context[(foo ?A ?B ?C)] ] =>
      idtac A; idtac B; idtac C
    end.

prints "a", "b" and "c" in consequtive lines. I can also say:

.. code-block:: coq

    match goal with
    | [ |- context[(foo ?A ?B ?C)] ] =>
      let d := fresh "d" in
      replace (foo A B C) with (fun d => foo A B C d) by auto
    end.

and this succeeds, but interestingly the goal remains unchaged, i.e.
the call is still in the form ``(foo a b c R)`` and not ``((fun d =>
foo a b c d) R)``. What am I doing wrong here?
|*)

(*|
Answer
******

The ``replace`` tactic performs β reduction. You can see this by
writing
|*)

Goal True.
  replace True with ((fun x => x) True) by auto.
Abort. (* .none *)

(*|
If you instead use the ``change`` tactic (which only works when
side-condition of ``replace`` could be solved by ``reflexivity``),
then it should work. For example,
|*)

Goal True.
  change True with ((fun x => x) True).

(*|
changes the goal to ``(fun x : Prop => x) True``.

This is undocumented, and I have reported it as `an issue on GitHub
<https://github.com/coq/coq/issues/6684>`__.
|*)
