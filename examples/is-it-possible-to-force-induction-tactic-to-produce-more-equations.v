(*|
###################################################################
Is it possible to force induction tactic to produce more equations?
###################################################################

:Link: https://stackoverflow.com/questions/52015166/is-it-possible-to-force-induction-tactic-to-produce-more-equations
|*)

(*|
Question
********

I'm playing with inductive propositions. I have the following inductive definition:
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Inductive subseq {X : Type} : list X -> list X -> Prop :=
| empty_subseq : subseq [] []
| subseq_left_elim : forall (l1 l2 : list X) (x : X),
    subseq (x :: l1) l2 -> subseq l1 l2
| subseq_intro : forall (l1 l2 : list X) (x : X),
    subseq l1 l2 -> subseq (x :: l1) (x :: l2).

Notation "l <<< k" := (subseq l k) (at level 10).

(*|
And I'm trying to prove such a lemma:

.. coq:: none
|*)

Lemma empty_subseq_l : forall (X : Type) (l : list X), [] <<< l.
Proof.
  intros. induction l; [apply empty_subseq |].
  apply subseq_left_elim with a. now apply subseq_intro.
Qed.

(*||*)

Lemma subseq_right_elim : forall (X : Type) (l1 l2 : list X) (x y : X),
    (x :: l1) <<< (y :: l2) -> x = y \/ (x :: l1) <<< l2.
Proof.
  intros X l1 l2 x y H.
  induction H as [| l1' l2' z E IH | l1' l2' z E IH].
  - right. apply empty_subseq_l.
  (* empty_subseq_l : forall (X : Type) (l : list X), [ ] <<< l. *)
  - destruct IH as [IH | IH].
    + left. apply IH.
    + right. apply subseq_left_elim with z. apply IH.
  - (* stuck *)
Abort.

(*|
I have no idea how to proof the ``subseq_intro`` case. It seems to be
true, because, informally, if the subseq_intro was applied to produce
``(x :: l1) <<< (y :: l2)``, then ``x`` and ``y`` must be equal and it
simply entails the goal. But Coq doesn't provide such assertions in
the third case. How to force it to do that, like if the inversion
tactic was applied?
|*)

(*|
Answer
******

How to get a solution for the original problem
==============================================

You can use `remember
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.remember>`__
tactic because ``induction`` (and ``destruct``) "forgets" the exact
shape of indices. And in the type ``arg1 <<< arg2``, both ``arg1`` and
``arg2`` are `indices
<https://stackoverflow.com/q/24600256/2747511>`__. Incidentally, `this
blog post
<https://homes.cs.washington.edu/~jrw12/dep-destruct.html>`__ by James
Wilcox explains how this works in detail. Anyways, if you want to do
induction on an inductive type family, you often want the indices to
be variables (with extra equations keeping all the information you
need).

So, if you start like so:

.. code-block:: coq

    remember (x :: l1) as xl1 eqn: E1.
    remember (y :: l2) as xl2 eqn: E2.

you get your equations, but you will eventually get into trouble
because the induction hypotheses won't be usable. To make them usable,
simply generalize the induction hypotheses by doing

.. code-block:: coq

    revert x y l1 l2 E1 E2.

More explicit, you start like so
|*)

Lemma subseq_right_elim (X : Type) (l1 l2 : list X) (x y : X) :
  (x :: l1) <<< (y :: l2) -> (x = y) \/ (x :: l1) <<< l2.
Proof.
  intros H.
  remember (x :: l1) as xl1 eqn: E1. remember (y :: l2) as xl2 eqn: E2.
  revert x y l1 l2 E1 E2.
  induction H as [| l1' l2' z S IH | l1' l2' z S IH]; intros x y l1 l2 E1 E2.
Abort. (* .none *)

(*|
For what it's worth, the statement of your lemma is not general
enough, so induction won't help -- this time you will be able to solve
the third subgoal, but not the second one. To overcome this
difficulty, make the lemma's statement more like ``subseq_left_elim``.

*SPOILER ALERT:* `this gist
<https://gist.github.com/anton-trunov/42fb0273cf8eb495f602fd3f41f9f32c>`__
has full proof.

A better way is to redefine inductive predicate
===============================================

Now, the difficulties you are experiencing stem from the roundabout
way to define the notion of being a subsequence. You can see it more
clearly from a proof of a very simple example:
|*)

Goal [1; 3; 5] <<< [0; 1; 2; 3; 4; 5; 6].
Proof.
  apply subseq_left_elim with 0. apply subseq_intro. apply subseq_intro.
  apply subseq_left_elim with 2. apply subseq_intro. apply subseq_intro.
  apply subseq_left_elim with 4. apply subseq_intro. apply subseq_intro.
  apply subseq_left_elim with 6. apply subseq_intro. apply empty_subseq.
Qed.

(*|
Basically, you have to grow the size of your goal to reduce it later.

Had you chosen a simpler encoding, e.g.
|*)

Reset subseq. (* .none *)
Reserved Notation "l <<< k" (at level 10).
Inductive subseq {X : Type} : list X -> list X -> Prop :=
| empty_subseq : [] <<< []
| subseq_drop_right l1 l2 x : l1 <<< l2 ->       l1  <<< (x :: l2)
| subseq_drop_both l1 l2 x  : l1 <<< l2 -> (x :: l1) <<< (x :: l2)
where "l <<< k" := (subseq l k).

(*|
your life would have been so much easier! E.g. here is a new proof of
the aforementioned simple fact:
|*)

Goal [1; 3; 5] <<< [0; 1; 2; 3; 4; 5; 6].
  apply subseq_drop_right. apply subseq_drop_both.
  apply subseq_drop_right. apply subseq_drop_both.
  apply subseq_drop_right. apply subseq_drop_both.
  apply subseq_drop_right. apply empty_subseq.
Qed.

(*|
This time you just make the goal smaller with every step you take.
|*)
