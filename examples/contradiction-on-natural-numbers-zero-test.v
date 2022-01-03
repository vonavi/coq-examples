(*|
###########################################
Contradiction on natural number's zero test
###########################################

:Link: https://stackoverflow.com/q/58245731
|*)

(*|
Question
********

I have a natural number that is not equal to zero. I want to prove
that if it is equal to zero then it give false.
|*)

Require Import PeanoNat. (* .none *)
Lemma notzero : forall n, n <> 0 -> (n =? 0) = false.
Proof.
  intros n H. Fail inversion H. (* .fails *)

(*|
Answer (larsr)
**************

Instead of using inversion in every proof, I find that the proofs are
more maintainable in the long run if you use boolean reflection. The
libraries have many useful lemmas that you can use, they often are
called something with "reflect", "decide", "dec" or "spec" as in
specification, so you can i.e. search for lemmas related to ``<`` with
``Search (_ < _) "spec"``.

The reflection lemmas are designed to at the same time 1) destruct the
boolean term in your proof context, and 2) add the corresponding
``Prop`` to your context, making it easy to then use ``lia``,
``omega``, etc. to finish the proof.

In your case, you can use ``Nat.eqb_spec`` (from ``Require Import
PeanoNat.``). Do
|*)

  destruct (Nat.eqb_spec n 0). Undo. (* .none *)

(*|
It will create two branches, in one ``n ?= 0`` is replaced with
``true`` and ``n = 0`` is added to the context, and in the other ``n
=? 0`` is replaced with ``false`` and ``n <> 0`` is added to the
context. It is now very easy to finish of the proof, as the first
goal's context contains the contradiction ``n = 0`` and ``n <> 0``,
and the second goal is ``false = false``. You can use the automation
tactical ``now``, so the complete proof is
|*)

  now destruct (Nat.eqb_spec n 0).

(*|
If you want to use integers ``Z``, instead, the proof becomes ``now
destruct (Z.eq_spec n 0).``. as the ``Z`` module has many of the
corresponding lemmas with matching names.
|*)

Qed. (* .none *)

(*|
Answer (Théo Winterhalter)
**************************

Generally, you can use the fact that ``=?`` reflects equality on
natural numbers (``Nat.eqb_spec``). Are you using the two notions of
equality on purpose? Note that ``n <> 0`` is a notation for ``n = 0 ->
False``.
|*)

Reset notzero. (* .none *)
Lemma notzero : forall n, n <> 0 -> (n =? 0) = false.
Proof.
  intros n h. destruct (Nat.eqb_spec n 0).
  - exfalso. apply h. assumption.
  - reflexivity.
Qed.

(*|
There is also the possibility of simply doing an analysis on ``n``. If
it is ``0`` then you can use your hypothesis to conclude, and if it is
some ``S m`` then your goal will be provable by ``reflexivity``.
|*)

Reset notzero. (* .none *)
Lemma notzero : forall n, n <> 0 -> n =? 0 = false.
Proof.
  intros n h. destruct n.
  - contradiction.
  - reflexivity.
Qed.
