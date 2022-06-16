(*|
###################################
How to do "negative" match in Ltac?
###################################

:Link: https://stackoverflow.com/q/28412816
|*)

(*|
Question
********

I want to apply a rule in a case when some hypothesis present, and
another is not. How can I check for this condition?

For example:
|*)

Variables X Y Z : Prop.
Axiom A : X -> Y.
Axiom B : X -> Z.
Ltac more_detail := idtac. (* .none *)

(*|
.. code-block:: coq

    Ltac more_detail :=
      match goal with
      | [H1 : X, <not H2 : Y> |- _]  =>
          let H' := fresh "DET" in assert Y as H'
              by (apply A; assumption)
      | [H1 : X, <not H2 : Z> |- _]  =>
          let H' := fresh "DET" in assert Z as H'
              by (apply B; assumption)
      end.

Such that, for this goal:
|*)

Goal X -> True.
  intros.
  Show. (* .unfold .messages *)

(*| ``more_detail.`` would introduce a second hypothesis ``DET``: |*)

  assert Y as DET by (apply A; assumption). (* .none *)
  assert Z as DET0 by (apply B; assumption). (* .none *)
  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
And a successive invocation ``more_detail.`` would fail.

However ``more_detail.`` should always ensure, that both ``Y`` and
``Z`` are there, i.e. if only one of them present, it should run a
rule for another:
|*)

Goal X -> Y -> True.
  intros.
  Show. (* .unfold .messages *)
  assert Z as DET by (apply B; assumption). (* .none *)
  more_detail.
  Show. (* .unfold .messages *)
Abort. (* .none *)

Goal X -> Z -> True.
  intros.
  Show. (* .unfold .messages *)
  assert Y as DET by (apply A; assumption). (* .none *)
  more_detail.
  Show. (* .unfold .messages *)

(*|
Answer
******

This is a common Ltac pattern. You can use the ``fail`` tactic to
avoid executing a branch when some condition matches:
|*)

Reset Initial. (* .none *)
Variables X Y Z : Prop.
Hypothesis A : X -> Y.
Hypothesis B : X -> Z.

Ltac does_not_have Z :=
  match goal with
  | _ : Z |- _ => fail 1
  | |- _ => idtac
  end.

Ltac more_detail :=
  match goal with
  | H : X |- _ =>
      first [ does_not_have Y;
              let DET := fresh "DET" in
              assert (DET := A H)
            | does_not_have Z;
              let DET := fresh "DET" in
              assert (DET := B H) ]
  end.

Goal X -> True.
  intros H. more_detail. more_detail.
  (* This fails *)
  Fail more_detail. (* .fails *)
Abort.

(*|
The ``does_not_have`` tactic acts as a negative match: it only
succeeds if its argument is not present in the context. Here's how it
works: if ``H : Z`` is present in the context, the first branch will
match. Calling simply ``fail`` or ``fail 0`` would cause that branch
to fail, but would allow Ltac to try other branches of the same
``match``. Using ``fail 1`` causes the current branch and the entire
match to fail. If ``H : Z`` is not present in the context, the first
branch will never match, and Coq will skip it and try the second
branch. Since this branch doesn't do anything, execution will proceed
with whichever tactics come after the ``match``.

In ``more_detail``, the ``first`` tactical can be used to combine
several invocations of ``does_not_have``; since each branch of
``first`` will fail if the context contains the corresponding
hypothesis, the construction as a whole will have the effect of your
``match`` with negative patterns.
|*)
