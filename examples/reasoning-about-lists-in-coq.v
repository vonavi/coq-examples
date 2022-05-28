(*|
############################
Reasoning about lists in Coq
############################

:Link: https://stackoverflow.com/q/34493687
|*)

(*|
Question
********

I'm try to solve some theorems, based on Pierce's "Software
Foundations".

First of all I create a couple of useful functions:
|*)

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Theorem count_repeat : forall n : nat, length (repeat n n) = n.
Proof.
  intros n. induction n as [| n'].
  - reflexivity.
  - simpl. (* and here I can't continue... *)
Abort. (* .none *)

(*|
I want to follow Pierce's advice:

    Note that, since this problem is somewhat open-ended, it's
    possible that you may come up with a theorem which is true, but
    whose proof requires techniques you haven't learned yet. Feel free
    to ask for help if you get stuck!

So, could you please advice some proof techniques for me?

----

**A (eponier):** The two arguments of ``repeat`` do not have the same
meaning at all. In particular, in your theorem, the values of the list
are not important. You should try to prove a more general lemma using
distinct variables for the values and the length.
|*)

(*|
Answer
******

As @eponier said, you should try to prove a more general lemma, like
|*)

Theorem count_repeat_gen : forall m n : nat, length (repeat n m) = m.

(*|
Using ``repeat n n`` creates an implicit link between the value of the
element and the size of the list which makes your statement impossible
to prove directly. Once you proved ``count_repeat_gen``, you'll be
able to prove your theorem.
|*)
