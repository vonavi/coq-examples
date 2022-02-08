(*|
##############################
Teach coq to check termination
##############################

:Link: https://stackoverflow.com/q/48173854
|*)

(*|
Question
********

Coq, unlike many others, accepts an optional explicit parameter, which
can be used to indicate the decreasing structure of a fixpoint
definition.

From Gallina specification, 1.3.4,

.. code-block:: coq

    Fixpoint ident params {struct ident0} : type0 := term0

defines the syntax. but from it, we've known that it must be an
identifier, instead of a general measure.

However, in general, there are recursive functions, that the
termination is not quite obvious, or it in fact is, but just difficult
for the termination checker to find a decreasing structure. For
example, following program interleaves two lists,
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Fail Fixpoint interleave (A : Set) (l1 l2 : list A) : list A :=
  match l1 with
  | [] => []
  | h :: t => h :: interleave l2 t
  end. (* .fails *)

(*|
This function clearly terminates, while Coq just couldn't figure it
out. The reason is neither ``l1`` nor ``l2`` are decreasing every
cycle. But what if we consider a measure, defined to be ``length l1 +
length l2``? Then this measure clearly decreases every recursion.

So my question is, in the case of sophisticated situation, where code
is not straightforward to be organized in a termination checkable way,
how do you educate coq and convince it to accept the fixpoint
definition?
|*)

(*|
Answer
******

You have multiple options and all of them boil down to structural
recursion in the end.

Preamble
========
|*)

Reset Initial. (* .none *)
From Coq Require Import List.
Import ListNotations.
Set Implicit Arguments.

(*|
Structural recursion
====================

Sometimes you can reformulate your algorithm in a structurally
recursive way:
|*)

Fixpoint interleave1 {A} (l1 l2 : list A) {struct l1} : list A :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 => h1 :: h2 :: interleave1 t1 t2
  end.

(*|
Incidentally, in some cases you can use a trick with nested ``fix``\
es -- see `this definition of Ackermann function
<https://stackoverflow.com/a/10303475/2747511>`__ (it wouldn't work
with just ``Fixpoint``).

``Program Fixpoint``
====================

You can use ``Program Fixpoint`` mechanism which lets you write your
program naturally and later prove that it always terminates.
|*)

From Coq Require Import Program Arith.

Program Fixpoint interleave2 {A} (l1 l2 : list A)
        {measure (length l1 + length l2)} : list A :=
  match l1 with
  | [] => l2
  | h :: t => h :: interleave2 l2 t
  end.
Next Obligation. simpl. rewrite Nat.add_comm. trivial with arith. Qed.

(*|
``Function``
============

Another option is to use the ``Function`` command which can be
somewhat limited compared to ``Program Fixpoint``. You can find out
more about their differences `here
<https://stackoverflow.com/q/44606245/2747511>`__.
|*)

From Coq Require Recdef.

Definition sum_len {A} (ls : (list A * list A)) : nat :=
  length (fst ls) + length (snd ls).

Function interleave3 {A} (ls : (list A * list A))
         {measure sum_len ls} : list A :=
  match ls with
  | ([], _) => []
  | (h :: t, l2) => h :: interleave3 (l2, t)
  end.
Proof.
  intros A ls l1 l2 h t -> ->. unfold sum_len.
  simpl. rewrite Nat.add_comm. trivial with arith.
Defined.

(*|
`Equations <http://mattam82.github.io/Coq-Equations/>`__ plugin
===============================================================

This is an external plugin which addresses many issues with defining
functions in Coq, including dependent types and termination.
|*)

From Equations Require Import Equations.

Equations interleave4 {A} (l1 l2 : list A) : list A
  by wf (length l1 + length l2) lt :=
  interleave4 nil l2 := l2;
  interleave4 (cons h t) l2 := cons h (interleave4 l2 t).
Next Obligation. rewrite Nat.add_comm. trivial with arith. Qed.

(*|
``Fix`` / ``Fix_F_2`` combinators
=================================

You can learn more about this (manual) approach if you follow the
links from `this question
<https://stackoverflow.com/q/42285235/2747511>`__ about ``mergeSort``
function. By the way, the ``mergeSort`` function can be defined
without using ``Fix`` if you apply the nested ``fix`` trick I
mentioned earlier. Here is a solution which uses ``Fix_F_2``
combinator since we have two arguments and not one like ``mergeSort``:
|*)

Definition ordering {A} (l1 l2 : list A * list A) : Prop :=
  length (fst l1) + length (snd l1) < length (fst l2) + length (snd l2).

Lemma ordering_wf' {A} : forall (m : nat) (p : list A * list A),
    length (fst p) + length (snd p) <= m -> Acc (@ordering A) p.
Proof.
  unfold ordering. induction m; intros p H; constructor; intros p'.
  - apply Nat.le_0_r, Nat.eq_add_0 in H as [-> ->].
    intros contra%Nat.nlt_0_r. contradiction.
  - intros H'. eapply IHm, Nat.lt_succ_r, Nat.lt_le_trans; eauto.
Defined.

Lemma ordering_wf {A} : well_founded (@ordering A).
Proof. now red; intro; eapply ordering_wf'. Defined.

(* it's in the stdlib but unfortunately opaque -- this blocks evaluation *)
Lemma destruct_list {A} (l : list A) :
  { x : A & {tl : list A | l = x :: tl} } + { l = [] }.
Proof.
  induction l as [|h tl]; [right | left]; trivial.
  exists h, tl. reflexivity.
Defined.

Definition interleave5 {A} (xs ys : list A) : list A.
  refine (Fix_F_2
            (fun _ _ => list A)
            (fun (l1 l2 : list A)
                 (interleave :
                    (forall l1' l2', ordering (l1', l2') (l1, l2) -> list A)) =>
               match destruct_list l1 with
               | inright _ => l2
               | inleft pf => let '(existT _ h (exist _ tl eq)) := pf
                              in h :: interleave l2 tl _
               end) (ordering_wf (xs, ys))).
  Proof.
    unfold ordering. rewrite eq, Nat.add_comm. auto.
  Defined.

(*|
Evaluation tests
================
|*)

Check eq_refl : interleave1 [1; 2; 3] [4; 5; 6] = [1; 4; 2; 5; 3; 6].
Check eq_refl : interleave2 [1; 2; 3] [4; 5; 6] = [1; 4; 2; 5; 3; 6].
Check eq_refl : interleave3 ([1; 2; 3], [4; 5; 6]) = [1; 4; 2; 5; 3; 6].
Check eq_refl : interleave4 [1; 2; 3] [4; 5; 6] = [1; 4; 2; 5; 3; 6].
Check eq_refl : interleave5 [1; 2; 3] [4; 5; 6] = [1; 4; 2; 5; 3; 6].

(*|
Exercise: what happens with this last check if you comment out
``destruct_list`` lemma?
|*)
