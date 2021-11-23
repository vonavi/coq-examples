(*|
###############################
In-place simplification for Coq
###############################

:Link: https://stackoverflow.com/questions/61077944/in-place-simplification-for-coq
|*)

(*|
Question
********

I want this goal:
|*)

Require Import Lia. (* .none *)
Goal forall (A : Type) (j' : nat) (f : nat -> A), f (S j') = f (j' + 1).

(*| to be proven automatically by Coq. Currently I have to write: |*)

  intros. apply f_equal. lia.
  Restart. (* .none *)

(*|
But in general it can be more difficult and I might need to assert for
instance that ``m - 0 = m`` and then rewrite. Is there a way to
rewrite a term in-place, as Isabelle has?
|*)

(*|
Answer
******

I'm not sure exactly what you want. Perhaps the ``replace`` tactic can
be of help to you.

Basically you would write
|*)

  intros. replace (S j') with (j' + 1).
  - (* f (j' + 1) = f (j' + 1) *)
    reflexivity.
  - (* j' + 1 = S j' *)
    lia.
  Restart. (* .none *)

(*|
(Note that I'm using ``lia`` and not ``omega`` as ``omega`` is
deprecated in favour of ``lia``.)

You can even discharge the replacement directly by ``lia``:
|*)

  intros. replace (S j') with (j' + 1) by lia.
  reflexivity.

(*|
This way the replacement only succeeds if ``lia`` is able to solve the
needed equality.
|*)
