(*|
########################
Extensible tactic in Coq
########################

:Link: https://stackoverflow.com/questions/48868186/extensible-tactic-in-cow
|*)

(*|
Question
********

Let's say I have a fancy tactic that solves lemmas of a certain kind:

.. code-block:: coq

    Ltac solveFancy :=
      some_preparation;
      repeat (first [important_step1 | important_step2];
              some_cleanup);
      solve_basecase.

Now I use this tactic to prove further lemmas of that kind, which I
subsequently want to use in this tactic.

.. code-block::: coq

    Lemma fancy3 := ... Proof. ... Qed.
    Ltac important_step3 := apply fancy3;[some | specific | stuff].

Now I could simply re-define ``Ltac solveFancy ::= ...`` and add
``important_step3`` to the list, but that quickly gets old.

Is there a more elegant way of now extending the list of
``important_step``-tactics in ``solveFancy``? I am imagining something
like:

.. code-block:: coq

    Add Hint SolveFancy important_step3.
|*)

(*|
Answer (Tej Chajed)
*******************

It's not what I'd call elegant, but here's a pure Ltac solution. You
can leave a hook in your tactic which you re-define later, and you can
keep following this pattern by always leaving a hook for the next
hint:
|*)

Axiom P : nat -> Prop.
Axiom P0 : P 0.
Axiom P_ind : forall n, P n -> P (S n).

Ltac P_hook := fail.

Ltac solve_P :=
  try apply P_ind;
  exact P0 || P_hook.

Theorem ex_1 : P 1.
Proof.
  solve_P.
Qed.

Ltac P_hook2 := fail.
Ltac P_hook ::= exact ex_1 || P_hook2.

Theorem ex_2 : P 2.
Proof.
  solve_P.
Qed.

Ltac P_hook3 := fail.
Ltac P_hook ::= exact ex_2 || P_hook3.

Theorem ex_3 : P 3.
Proof.
  solve_P.
Qed.

(*|
There should be a way to do this with ``Hint Extern``, but it'll be
much harder to control when and in what order those hints are tried,
and they have to fully solve the goal by the end.
|*)

(*|
Answer (Lily Chung)
*******************

I would add an argument to ``solveFancy`` which you can use to pass in
another tactic:

.. code-block:: coq

    Ltac solveFancy hook :=
      some_preparation;
      repeat (first [important_step1 | important_step2 | hook];
              some_cleanup);
      solve_basecase.

    (* use solveFancy without any extra available steps *)
    [...] solveFancy fail [...]

    Ltac important_step3 := [...]

    (* use solveFancy with important_step3 *)
    [...] solveFancy important_step3 [...]

This is somewhat more elegant than redefining a hook, though it
doesn't solve the extensibility problem by itself. The following is a
strategy for repeatedly redefining a tactic ``x`` in terms of previous
versions of itself, using the fact that modules allow redefining an
Ltac name without overwriting the previous definition.
|*)

Ltac x := idtac "a".

Goal False.
  x. (* a *)
Abort.

Module K0.
  Ltac x' := x.
  Ltac x := x'; idtac "b".
End K0.
Import K0.

Goal False.
  x. (* a b *)
Abort.

Module K1.
  Ltac x' := x.
  Ltac x := x'; idtac "c".
End K1.
Import K1.

Goal False.
  x. (* a b c *)
Abort.

(*|
Note that the names ``K0``, ``K1`` of the modules don't matter and
they can be renamed or reordered however you want. This isn't the most
elegant thing in the world but I think it's an improvement.
|*)
