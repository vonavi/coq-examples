(*|
########################################
Pattern Matching with Even and Odd Cases
########################################

:Link: https://stackoverflow.com/q/46383481
|*)

(*|
Question
********

Suppose I write a Fixpoint algorithm in Coq that sums up all the
"halves" of a number:
|*)

Fail Fixpoint sum_of_halves (a : nat) : nat :=
  match a with
  | 0 => 0
  | 2 * k => a + (sum_of_halves k)
  | S (2 * k)  => a + (sum_of_halves k)
  end. (* .unfold .fails *)

(*|
How can I get Coq to recognize that a is either an even or an odd
number, and match it with either ``2 * k`` or ``S (2 * k)``?
|*)

(*|
Answer (jbapple)
****************

Coq can only ``match`` on constructors. ``nat`` has two constructors,
``O`` and ``S``, so you cannot match on ``2 * k``. You will have to
use a non-``match`` construct or a non-``nat`` type or a different
algorithm.
|*)

(*|
Answer (Yves)
*************

You need to prove that there are only three cases for a given natural
number ``a``. Either ``a`` is 0, either ``a`` is the double of another
number ``k`` and ``k < a``, or ``a`` is the double ``k + 1`` and ``k <
a``, that the three cases are exclusive (this is important, otherwise
making pattern matching possible would lead to an inconsistency).

Fortunately, all this can be done. It is a bit advanced Coq
programming, but it is somehow already done in ``ZArith``. Here is a
solution.

First note that the other number is already provided by one of the
functions in the Coq library, ``div2``.
|*)

Require Import Arith Nat.

Definition cases_div2 (a : nat) :
  {k : nat | a = 2 * k /\ k < a} + {k : nat | a = S (2 * k) /\ k < a} + {a = 0}.
Proof.
  destruct a as [ | a'].
  - right. reflexivity.
  - case_eq (odd (S a')); intros odd_a.
    + left. right. exists (div2 (S a')).
      rewrite (Nat.div2_odd (S a')) at 1. split.
      * rewrite odd_a. simpl Nat.b2n. ring.
      * apply Nat.lt_div2. auto with arith.
    + left. left. exists (div2 (S a')).
      rewrite (Nat.div2_odd (S a')) at 1. split.
      * rewrite odd_a. simpl Nat.b2n. ring.
      * apply Nat.lt_div2. auto with arith.
Defined.

(*|
Now, you can pattern match on your number a using ``cases_div2``, but
it is still not enough to define your function, because recursion
using ``Fixpoint`` relies on recursive calls happening on the
predecessor, and here ``k`` cannot be written as a predecessor pattern
that will work for any input ``a``. You need a stronger kind of
recursion. I usually rely on ``Function`` or ``Fix`` for this kind of
strong recursion. Here is an example with ``Fix``:
|*)

Definition sum_of_halves : nat -> nat :=
  Fix Arith.Wf_nat.lt_wf (fun _ => nat)
      (fun a (sum_of_halves' : forall y, y < a -> nat) =>
         match cases_div2 a with
         | inright h => 0
         | inleft (inl (exist _ k (conj keq klt))) =>
             a + sum_of_halves' k klt
         | inleft (inr (exist _ k (conj keq klt))) =>
             a + sum_of_halves' k klt
         end).

(*|
Then to reason about ``sum_of_halves`` you will need to reason by well
founded induction and use ``Fix_eq``.

This is one possibility.
|*)
