(*|
###################################
Generalising a set of proofs in coq
###################################

:Link: https://stackoverflow.com/questions/53204593/generalising-a-set-of-proofs-in-coq
|*)

(*|
Question
********

I am trying to complete the first part lab of the 6.826 MIT course,
but I am unsure about a comment above one of the exercises that says I
can solve a bunch of examples using the same proof. here is what i
mean:
|*)

Require Import FunInd. (* .none *)
(* A `nattree` is a tree of natural numbers, where every internal node
   has an associated number and leaves are empty. There are two
   constructors, L (empty leaf) and I (internal node). I's arguments
   are: left-subtree, number, right-subtree. *)
Inductive nattree : Set :=
| L : nattree                               (* Leaf *)
| I : nattree -> nat -> nattree -> nattree. (* Internal nodes *)

(* Some example nattrees. *)
Definition empty_nattree := L.
Definition singleton_nattree := I L 0 L.
Definition right_nattree := I L 0 (I L 1 (I L 2 (I L 3 L))).
Definition left_nattree := I (I (I (I L 0 L) 1 L) 2 L) 3 L.
Definition balanced_nattree := I (I L 0 (I L 1 L)) 2 (I L 3 L).
Definition unsorted_nattree := I (I L 3 (I L 1 L)) 0 (I L 2 L).

(* EXERCISE: Complete this proposition, which should be `True` iff `x`
   is located somewhere in `t` (even if `t` is unsorted, i.e., not a
   valid binary search tree). *)
Function btree_in (x : nat) (t : nattree) : Prop :=
  match t with
  | L => False
  | I l n r => n = x \/ btree_in x l \/ btree_in x r
  end.

(* EXERCISE: Complete these examples, which show `btree_in` works.
   Hint: The same proof will work for every example. End each example
   with `Qed.`. *)
Example btree_in_ex1 : ~ btree_in 0 empty_nattree.
Proof.
  simpl. auto.
Qed.
Example btree_in_ex2 : btree_in 0 singleton_nattree.
Proof.
  simpl. auto.
Qed.
Example btree_in_ex3 : btree_in 2 right_nattree.
Proof.
  simpl. right. auto.
Qed.
Example btree_in_ex4 : btree_in 2 left_nattree.
Proof.
  simpl. right. auto.
Qed.
Example btree_in_ex5 : btree_in 2 balanced_nattree.
Proof.
  simpl. auto.
Qed.
Example btree_in_ex6 : btree_in 2 unsorted_nattree.
Proof.
  simpl. auto.
Qed.
Example btree_in_ex7 : ~ btree_in 10 balanced_nattree.
Proof.
  simpl. intros G. destruct G. inversion H. destruct H. destruct H. inversion H.
  destruct H. inversion H. destruct H. inversion H. destruct H. inversion H.
  destruct H. destruct H. inversion H. destruct H. inversion H. destruct H.
Qed.
Example btree_in_ex8 : btree_in 3 unsorted_nattree.
Proof.
  simpl. auto.
Qed.

(*|
The code under the comments ``EXERCISE`` have been completed as an
exercise (though ``ex7`` required some googling...), the hint for the
second exercise says 'Hint: The same proof will work for every
example.' but i'm unsure how to write a proof for each one that isn't
specific to that case.

The course material in question can be found here:
http://6826.csail.mit.edu/2017/lab/lab0.html

As a beginner with Coq I'd appreciate being steered in the right
direction as opposed to just being given a solution. If there is a
particular tactic that would be useful here that I am perhaps missing
it would be good to be pointed towards that...
|*)

(*|
Answer
******

I think you're just missing the ``intuition`` tactic, which
``intro``'s hypotheses when it sees ``A -> B``, unfolds ``~ P`` to ``P
-> False`` and ``intro``'s that, splits ``/\``'s and ``\/``'s in the
hypotheses, breaks ``/\``'s in the goal into multiple subgoals, and
uses ``auto`` to search both branches of ``\/``'s in the goal. That
may seem like a lot but note that these are all basic strategies from
logic (other than the call to ``auto``).

After you run simpl on each of these exercises you'll see it fits this
form and then ``intuition`` will work.
|*)
