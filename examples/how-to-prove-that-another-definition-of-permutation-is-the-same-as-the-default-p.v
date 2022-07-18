(*|
##########################################################################################################
How to prove that another definition of permutation is the same as the Default Permutation Library for Coq
##########################################################################################################

:Link: https://stackoverflow.com/q/71083370
|*)

(*|
Question
********

I need to proove that a secondary definition of permutation is
equivalent to the default definition of permutation in Coq:

Down bellow is the default Permutation definition in Coq

.. coq:: none
|*)

Require Import List.
Import ListNotations.

Definition A := nat.

(*||*)

Inductive Permutation : list A -> list A -> Prop :=
| perm_nil : Permutation [] []
| perm_skip x l l' : Permutation l l' -> Permutation (x :: l) (x :: l')
| perm_swap x y l : Permutation (y :: x :: l) (x :: y :: l)
| perm_trans l l' l'' :
  Permutation l l' -> Permutation l' l'' -> Permutation l l''.

(*|
I need to prove that the above mentioned definition is equivalent to
the following definition:

.. coq:: none
|*)

Require Import PeanoNat.

Fixpoint occurences_number x l :=
  match l with
  | nil => 0
  | h :: tl => if (x =? h)
               then S (occurences_number x tl)
               else occurences_number x tl
  end.

(*||*)

Definition perm l l' := forall x, occurences_number x l = occurences_number x l'.

(*|
Which as you have noticed uses the definition ``occurences_number``
down bellow:
|*)

Reset occurences_number. (* .none *)
Fixpoint occurences_number x l :=
  match l with
  | nil => 0
  | h :: tl => if (x =? h)
               then S (occurences_number x tl)
               else occurences_number x tl
  end.

(*| .. coq:: none |*)

Definition perm l l' := forall x, occurences_number x l = occurences_number x l'.

(*| What I need to prove indeed is the following: |*)

Lemma permutation_to_perm : forall l l', Permutation l l' -> perm l l'.

(*| Down bellow is my incomplete proof |*)

Proof.
  induction l.
  - admit.
  - intros l' Hequiv.
    generalize dependent a.
    generalize dependent l.
    case l'.
    + Admitted.

(*|
----

**A (Arthur Azevedo De Amorim):** It is probably easier to do
induction on the hypothesis ``Permutation l l'`` instead of ``l``.

**Q:** What do you mean @ArthurAzevedoDeAmorim?

**A (Arthur Azevedo De Amorim):** In Coq, you can do induction not
only on data structures, but also on hypotheses that state inductively
defined propositions. If you are not familiar with this concept, I
recommend having a look at the Software Foundations book:
https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html#lab216
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

Here is a proof that follows the strategy I outlined above:
|*)

Lemma Permutation_to_perm l l' : Permutation l l' -> perm l l'.
Proof.
  intros H. induction H as [| x l1 l2 _ IH | x y l | l1 l2 l3 _ IH1 _ IH2 ].
  - intros ?; reflexivity.
  - intros y. simpl. now rewrite IH.
  - intros z. simpl. now destruct (z =? y), (z =? x).
  - intros ?. now rewrite IH1.
Qed.
