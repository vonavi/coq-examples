(*|
###################################################################
How can I implement a Coq tactic that iterates over the hypotheses?
###################################################################

:Link: https://stackoverflow.com/q/42709481
|*)

(*|
Question
********

As minimal example for my general question, suppose we have the
following:
|*)

Parameter C : Prop.

Definition blah := C.

(*|
I would like to implement a tactic that automatically unfolds ``blah``
in all hypotheses of the goal.

I tried this:
|*)

Ltac my_auto_unfold :=
  repeat match goal with
         | [ H: ?P |- ?P ] => unfold blah in H
         end.

Theorem g : blah -> blah -> blah.
Proof.
  intros. my_auto_unfold.
Abort. (* .none *)

(*| But only one hypothesis had ``blah`` unfolded. |*)

(*|
Answer
******

I think you may be looking for the ``progress`` tactical. If you do
this:
|*)

Reset my_auto_unfold. (* .none *)
Ltac my_auto_unfold :=
  repeat match goal with
         | [ H: ?P |- ?P ] => progress unfold blah in H
         end.

(*|
then it will unfold ``blah`` in both hypotheses. You can even do:
|*)

Ltac in_all_hyps tac :=
  repeat match goal with
         | [ H : _ |- _ ] => progress tac H
         end.

(*|
to generalize this pattern. Note that this may run the tactic in each
hypothesis multiple times.

----

If you want to run over all the hypotheses once, in order, this is
significantly harder (especially if you want to preserve evar contexts
and not add dumb stuff to the proof term). Here is the quick-and-dirty
way to do that (assuming your tactic doesn't mess with the goal):
|*)

Reset Initial. (* .none *)
Parameter C : Prop.
Definition blah := C.

Definition BLOCK := True.

Ltac repeat_until_block tac :=
  lazymatch goal with
  | [ |- BLOCK -> _ ] => intros _
  | [ |- _ ] => tac (); repeat_until_block tac
  end.

Ltac on_each_hyp_once tac :=
  generalize (I : BLOCK);
  repeat match goal with
         | [ H : _ |- _ ] => revert H
         end;
  repeat_until_block
    ltac:(fun _
          => intro;
             lazymatch goal with
             | [ H : _ |- _ ] => tac H
             end).

Theorem g : blah -> blah -> fst (id blah, True).
Proof.
  intros.
  on_each_hyp_once ltac:(fun H => unfold blah in H).
Abort. (* .none *)

(*|
The idea is that you insert a dummy identifier to mark where you are
in the goal (i.e., to mark how many variables can be introduced), and
then you revert all of the context into the goal, so that you can
reintroduce the context one hypothesis at a time, running the tactic
on each hypothesis you just introduced.
|*)
