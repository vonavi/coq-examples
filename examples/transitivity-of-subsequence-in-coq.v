(*|
Transitivity of subsequence in COQ
==================================

https://stackoverflow.com/questions/69797654/transitivity-of-subsequence-in-coq
|*)

(*|
Question
--------

I have been working my way through logical foundations and have gotten
very stuck on the transitivity of subsequences exercise.

Exercise: 2 stars, advanced (subsequence)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A list is a *subsequence* of another list if all of the elements in
the first list occur in the same order in the second list, possibly
with some extra elements in between. For example,

(Optional, harder) Prove `subseq_trans` that subsequence is transitive
-- that is, if `l1` is a subsequence of `l2` and `l2` is a subsequence
of `l3`, then `l1` is a subsequence of `l3`. Hint: choose your
induction carefully!

.. coq:: none
|*)

Require Import List.
Import ListNotations.

(*||*)

Inductive subseq : list nat -> list nat -> Prop :=
| sseq_e (l2 : list nat) : subseq [] l2
| sseq_m (l1 l2 : list nat) (n : nat) (H: subseq l1 l2) : subseq (n::l1) (n::l2)
| sseq_nm (l1 l2 : list nat) (n : nat) (H: subseq l1 l2) : subseq l1 (n::l2).

Theorem subseq_trans : forall l1 l2 l3 : list nat,
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3 H H0. induction H.
  - apply sseq_e.
  - induction l3.
    + inversion H0.
    + inversion H0.
      * apply sseq_m.
Abort. (* .none *)

(*|
I am having trouble getting the right induction hypothesis after
having tried a couple of different approaches. I have tried a number
of approaches and end up with a situation where, in my assumptions, I
have something like `subseq l2 (x::l3)` but then I need to prove
`subseq l2 l3` which seems like a dead end. Any pointers in the right
direction would be much appreciated.
|*)

(*|
Answer
------

That experience suggests generalizing the induction hypothesis over `l3`.
|*)

Theorem subseq_trans : forall l1 l2 l3 : list nat,
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3 H. generalize dependent l3. induction H; intros l3 H0.
  - apply sseq_e.
  - induction l3.
    + inversion H0.
    + inversion H0.
      * specialize (IHsubseq l3 H2). apply (sseq_m l1 l3 a IHsubseq).
      * specialize (IHl3 H3). apply (sseq_nm (n :: l1) l3 a IHl3).
  - induction l3.
    + inversion H0.
    + inversion H0.
      * specialize (IHsubseq l3 H2). apply (sseq_nm l1 l3 a IHsubseq).
      * specialize (IHl3 H3). apply (sseq_nm l1 l3 a IHl3).
Qed.
