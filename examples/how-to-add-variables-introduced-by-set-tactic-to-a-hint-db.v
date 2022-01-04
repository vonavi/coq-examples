(*|
###########################################################
How to add variables introduced by set tactic to a Hint DB?
###########################################################

:Link: https://stackoverflow.com/q/48114995
|*)

(*|
Question
********

I want to use a Hint DB with variables introduced by ``set``. For
example,
|*)

Example foo : forall n : nat, n + n = n + n.
Proof.
  intro.
  set (m := n + n).
Abort. (* .none *)
Fail #[local] Hint Unfold m : core. (* .fails .unfold *)

(*| Is there any way to achieve this, or is it impossible? |*)

(*|
Answer
******

It's not possible to do this like you suggested because after you
finish ``foo`` with ``Qed`` the local variable ``m`` will be out of
scope, but hints go straight into some global database.

However, you can use the ``Section`` mechanism, as the hints declared
inside a section are *local* to that section:
|*)

Section LocalHints.
  Variable n : nat.
  Let m := n + n.
  Hint Unfold m.

  Example bar : m = m.
  Proof.
    autounfold with core.
    reflexivity.
  Qed.
End LocalHints.
