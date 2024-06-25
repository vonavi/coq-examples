(*|
###################################################
How to do induction on the length of a list in Coq?
###################################################

:Link: https://stackoverflow.com/q/45872719
|*)

(*|
Question
********

When reasoning on paper, I often use arguments by induction on the
length of some list. I want to formalized these arguments in Coq, but
there doesn't seem to be any built in way to do induction on the
length of a list.

How should I perform such an induction?

More concretely, I am trying to prove `this theorem
<http://pastebin.ubuntu.com/25386445/>`__. On paper, I proved it by
induction on the length of ``w``. My goal is to formalize this proof
in Coq.
|*)

(*|
Answer (Yves)
*************

There are many general patterns of induction like this one that can be
covered by the existing library on well founded induction. In this
case, you can prove any property ``P`` by induction on length of lists
by using ``well_founded_induction``, ``wf_inverse_image``, and
``PeanoNat.Nat.lt_wf_0``, as in the following command:

.. coq:: none
|*)

Require Import Wellfounded.

Goal forall {T : Type} (l : list T) (P : list T -> Prop), P l.
Proof.
  intros T l P.

(*||*)

  induction l using (well_founded_induction
                       (wf_inverse_image _ nat _ (@length _)
                                         PeanoNat.Nat.lt_wf_0)).
Abort. (* .none *)

(*|
if you are working with lists of type ``T`` and proving a goal ``P
l``, this generates an hypothesis of the form

.. code-block:: coq

    H : forall y : list T, length y < length l -> P y

This will apply to any other datatype (like trees for instance) as
long as you can map that other datatype to ``nat`` using any size
function from that datatype to ``nat`` instead of ``length``.

Note that you need to add ``Require Import Wellfounded.`` at the head
of your development for this to work.

----

**A:** Here is a slightly shorter variant:

.. coq:: none
|*)

Require Import Coq.Arith.Wf_nat.

Goal forall {T : Type} (xs : list T) (P : list T -> Prop), P xs.
Proof.
  intros T xs P.

(*||*)

  induction xs using (induction_ltof1 _ (@length _)); unfold ltof in *.

(*| But I'd prefer explicit naming: |*)

  Undo. (* .none *)
  induction xs as [xs IHxs] using (induction_ltof1 _ (@length _));
    unfold ltof in IHxs.
Abort. (* .none *)

(*|
Answer (James Wilcox)
*********************

Here is how to prove a general list-length induction principle.
|*)

Reset Initial. (* .none *)
Require Import List Lia.

Section list_length_ind.
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
    assert (forall xs l : list A, length l <= length xs -> P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. lia.
      - apply IHxs. simpl in Hlen. lia.
    }
    intros xs. apply H_ind with (xs := xs). lia.
  Qed.
End list_length_ind.

(*|
You can use it like this

.. code-block:: coq

    Theorem foo : forall l : list nat, ...
    Proof.
      induction l using list_length_ind.
      ...

That said, your concrete example example does not necessarily need
induction on the length. You just need a sufficiently general
induction hypothesis.
|*)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

(* ... some definitions elided here ... *)

(*| .. coq:: none |*)

Inductive state : Type :=
| A: state
| B: state.

Inductive input : Type :=
| zero: input
| one: input.

(*||*)

Definition flip_state (s : state) :=
  match s with
  | A => B
  | B => A
  end.

Definition delta (s : state) (n : input) : state :=
  match n with
  | zero => s
  | one => flip_state s
  end.

(* ...some more definitions elided here ...*)

(*| .. coq:: none |*)

Fixpoint extend_delta (s : state) (w : list input) : state :=
  match w with
  | [] => s
  | n :: tl => delta (extend_delta s tl) n
  end.

Fixpoint one_num (w : list input) : nat :=
  match w with
  | [] => 0
  | one :: tl => S (one_num tl)
  | zero :: tl => one_num tl
  end.

(*||*)

Theorem automata221 : forall (w : list input),
    extend_delta A w = B <-> Nat.odd (one_num w) = true.
Proof.
  assert (forall w s, extend_delta s w = if Nat.odd (one_num w)
                                         then flip_state s
                                         else s).
  { induction w as [|i w]; intros s; simpl.
    - reflexivity.
    - rewrite IHw. destruct i; simpl.
      + reflexivity.
      + rewrite <- Nat.negb_even, Nat.odd_succ.
        destruct (Nat.even (one_num w)), s; reflexivity.
  }
  intros w. rewrite H. simpl.
  destruct (Nat.odd (one_num w)); intuition congruence.
Qed.

(*|
Answer (ejgallego)
******************

In case like this, it is often faster to generalize your lemma
directly:
|*)

Reset Initial. (* .none *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SO.

  Variable T : Type.
  Implicit Types (s : seq T) (P : seq T -> Prop).

  Lemma test P s : P s.
  Proof.
    move: {2}(size _) (leqnn (size s)) => ss; elim: ss s => [|ss ihss] s hs.
  Admitted. (* .none *)

End SO.

(*|
Just introduce a fresh ``nat`` for the size of the list, and regular
induction will work.
|*)
