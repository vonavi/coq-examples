(*|
######################################################################################################
Finding a well founded relation to prove termination of a function that stops decreasing at some point
######################################################################################################

:Link: https://stackoverflow.com/q/48121413
|*)

(*|
Question
********

Suppose we have:

.. coq:: none
|*)

Require Import List.
Import ListNotations.

Variable f : nat.
Variable R : nat -> nat -> Prop.

(*||*)

Require Import ZArith Program.
Open Scope Z_scope.

Program Fixpoint range (from to : Z) {measure f R} : list Z :=
  if from <? to
  then from :: range (from + 1) to
  else [].

(*|
I'd like to convince Coq that this terminates - I tried by measuring
the size of the range as ``abs (to - from)``. However, this doesn't
quite work because once the range is empty (that is, ``from >= to``),
it simply starts increasing once again.

Using my custom:
|*)

Definition preceeds_eq (l r : option nat) : Prop :=
  match l, r with
  | None, None     => False
  | None, Some _   => True
  | Some _, None   => False
  | Some x, Some y => (x < y)%nat
  end.

(*| and the cast: |*)

Definition Z_to_nat (z : Z) (p : 0 <= z) : nat.
Proof.
  dependent destruction z.
  - exact 0%nat.
  - exact (Pos.to_nat p).
  - assert (Z.neg p < 0) by apply Zlt_neg_0.
    contradiction.
Defined.

(*| I've also tried measuring with: |*)

Definition get_range (from to : Z) : option nat :=
  let range := (to - from) in
  if (range <? 0)
  then None
  else Some (Z_to_nat (Z.abs range) (Z.abs_nonneg range)).

(*|
But it runs into the issue that I cannot show that ``None < None`` and
using reflexive ``preceeds_eq`` makes the relation not well founded,
which brings me back to the same problem.

Is there a way to convince Coq that ``range`` terminates? Is my
approach completely broken?
|*)

(*|
Answer
******

If you map the length of you interval to ``nat`` using ``Z.abs_nat``
or ``Z.to_nat`` functions, and use a function deciding if the range is
not-empty with a more informative result type (``Z_lt_dec``) then the
solution becomes very simple:
|*)

Require Import ZArith Program.

Program Fixpoint range (from to : Z)
        {measure (Z.abs_nat (to - from))} : list Z :=
  if Z_lt_dec from to
  then from :: range (from + 1) to
  else [].
Next Obligation. apply Zabs_nat_lt. auto with zarith. Qed.

(*|
Using ``Z_lt_dec`` instead of its boolean counter-part gives you the
benefit of propagating the proof of ``from < to`` into the context,
which gives you the ability to deal with the proof obligation easily.

----

**A:** ``Z_lt_dec`` is a decision procedure too, but in addition to
marking the result as true or false (which are called ``left`` and
``right`` respectively) it also attaches a proof to the result. It's
quite suggestively called ``sumbool`` -- once I tried to explain its
usage in `this answer
<https://stackoverflow.com/a/42313822/2747511>`__ (in its second
half).
|*)
