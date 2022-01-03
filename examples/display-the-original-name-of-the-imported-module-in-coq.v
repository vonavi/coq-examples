(*|
#######################################################
Display the original name of the imported module in Coq
#######################################################

:Link: https://stackoverflow.com/q/52469003
|*)

(*|
Question
********

How to choose the textual representation of variables which belongs to
some module? (Please see commentaries inside the code below. It's like
Notation for modules.) I want to use it because it's preferable to see
the original meaning of the terms. (and separate different types with
the same realization: ``SetVars.t``, ``FuncSymb.t``, ``PredSymb.t``,
etc)
|*)

Require Import Coq.Structures.Equalities.
Require Import Arith.PeanoNat.

Module mod1 (SetVars : UsualDecidableTypeFull).
  Definition h : SetVars.t -> SetVars.t := fun x => x. (*example*)
End mod1.

Module mod2.
  Module SetVars := PeanoNat.Nat.
  Module X := mod1 SetVars.
  Import X.

  Theorem q : SetVars.t -> SetVars.t.
  Proof. exact h. Defined. (* Here everything is OK *)

  Check h. (*"h : nat -> nat"*)
  (*But I want to see "h : SetVars.t -> SetVars.t" *)
End mod2.

(*|
Answer
******

Replace

.. code-block:: coq

    Module SetVars := PeanoNat.Nat.

with

.. code-block:: coq

    Module SetVars : UsualDecidableTypeFull := PeanoNat.Nat.

This makes the module ``SetVars`` opaque, exposing exactly the
signature ``UsualDecidableTypeFull``, so that the type ``SetVars.t ->
SetVars.t`` can no longer be reduced.
|*)
