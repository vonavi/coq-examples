(*|
###############################
Ltac: optional arguments tactic
###############################

:Link: https://stackoverflow.com/q/44840624
|*)

(*|
Question
********

I want to make a Ltac tactic in coq which would take either 1 or 3
arguments. I have read about ``ltac_No_arg`` in the `LibTactics
<http://gallium.inria.fr/~fpottier/ssphs/LibTactics.html>`__ module
but if I understood it correctly I would have to invoke my tactic
with:

.. code-block:: coq

    mytactic arg_1 ltac_no_arg ltac_no_arg.

which is not very convenient.

Is there any way to get a result like this:

.. code-block:: coq

    mytactic arg_1.
    mytactic arg_1 arg_2 arg_3.
|*)

(*|
Answer
******

We can use the `Tactic Notation
<https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#coq:cmd.tactic-notation>`__
mechanism to try to solve your issue because it can handle variadic
arguments.

Let's reuse ``ltac_No_arg`` and define a dummy tactic ``mytactic`` for
the purposes of demonstration
|*)

Inductive ltac_No_arg : Set :=
| ltac_no_arg : ltac_No_arg.

Ltac mytactic x y z :=
  match type of y with
  | ltac_No_arg => idtac "x =" x (* a bunch of cases omitted *)
  | _ => idtac "x =" x "; y =" y "; z =" z
  end.

(*| Now let's define the aforementioned tactic notations: |*)

Tactic Notation "mytactic_notation" constr(x) :=
  mytactic x ltac_no_arg ltac_no_arg.
Tactic Notation "mytactic_notation" constr(x) constr(y) constr(z) :=
  mytactic x y z.

(*| Tests: |*)

Goal True.
  mytactic_notation 1.
  mytactic_notation 1 2 3.
Abort.
