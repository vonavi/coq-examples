(*|
#######################
Unfold notation in ltac
#######################

:Link: https://stackoverflow.com/q/48594507
|*)

(*|
Question
********

I noticed notations can be treated differently. For example ``<`` is
just notation for a regular definition and ``unfold "<"`` does work as
in the following example:
|*)

Theorem a : 4 < 5.
Proof.
  unfold "<". (* .unfold *)
Abort. (* .none *)

(*|
However, ``<=`` is notation associated with the type ``le`` and for
some reason ``unfold "<="`` doesn't work, as in the following example:
|*)

Theorem a : 4 <= 5.
Proof.
  Fail unfold "<=". (* .fails .unfold .no-goals *)
Abort. (* .none *)

(*|
Can I convert ``4 <= 5`` into ``le 4 5`` with some ltac command?
|*)

(*|
Answer (Anton Trunov)
*********************

This happens because ``<`` is interpreted as ``lt`` which is a
*definition* (`here
<https://coq.inria.fr/distrib/current/stdlib/Coq.Init.Peano.html#lt>`__):
|*)

Print lt. (* .unfold .no-in *)

(*|
You can achieve the same effect with ``unfold lt``.

In the same manner ``<=`` means ``le``, but you cannot unfold ``le``,
because it is a type constructor. The manual says that you can unfold
only a defined transparent constant or local definition.

The upshot here is that you don't unfold notations, you unfold the
definitions those notations refer to.
|*)

(*|
Answer (Yannick Forster)
************************

Adding to Anton's answer: If you already know how the notation is
defined and only want to make it visible in the goal, you could do
something like
|*)

Definition make_visible {X} (f : X) := f.

Notation "` f" := (make_visible f) (at level 5, format "` f").

Tactic Notation "unfold" "notation" constr(f) :=
  change f with (`f).
Tactic Notation "fold" "notation" constr(f) :=
  unfold make_visible.

Theorem a : 4 <= 5.
Proof.
  unfold notation le. (* .unfold *)
  fold notation le.
Abort. (* .none *)

(*| Edit: My first solution was |*)

Reset Initial. (* .none *)
Definition make_visible {X} (f : X) := (fun _ => f) tt.

(*| but, as Anton pointed out, this is easier. |*)
