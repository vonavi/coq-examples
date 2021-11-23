(*|
Improving dependently typed reverse function
============================================

:Link: https://stackoverflow.com/questions/63051692/improving-dependently-typed-reverse-function
|*)

(*|
Question
--------

Here is the code I have thus far:
|*)

Require Import PeanoNat. (* .none *)
Section ilist.
  Variable A: Set.

  Inductive ilist: nat -> Set :=
  | Nil : ilist O
  | Cons : forall {n}, A -> ilist n -> ilist (S n).

  (* not sure how to use in irev_aux *)
  Lemma same_length: forall n i2, ilist (n + S i2) = ilist (S n + i2).
  Proof.
    intros. rewrite Nat.add_succ_comm. reflexivity.
  Defined.

  Definition same_length' n i2 (l: ilist (n + S i2)): ilist (S n + i2).
    rewrite Nat.add_succ_comm. assumption.
  Defined.

  Fixpoint irev_aux {i1 i2} (ls: ilist i1): ilist i2 -> ilist (i1 + i2) :=
    match ls in ilist i1' return (ilist i2 -> ilist (i1' + i2)) with
    | Nil => fun rev => rev
    | Cons h t => fun rev => same_length' _ _ (irev_aux t (Cons h rev))
    end.

  Definition same_length'' n (l: ilist (n + 0)): ilist n.
  Proof.
    rewrite <- plus_n_O in l. assumption.
  Defined.

  Definition irev n (ls: ilist n): ilist n :=
    same_length'' n (irev_aux ls Nil).

End ilist.

(*|
This works! Which is an improvement from my previous attempts :) But
there are a couple less than desirable aspects that I'd like to try
and refine.

First, having a bunch of proofs hanging out to munge equivalent types
seems...annoying. Basically, ``same_length``, ``same_length'``,
``same_length''``. Perhaps this is an issue with how I defined
``irev_aux``, but I tried some definitions and others required a type
level match which seemed about as annoying.

I tried using ``refine``, but got a type error...is there a way to
invoke ``refine``, where you then have to prove that the types are in
fact equivalent? In a sense that's what I did, but who wants those
lemmas hanging out.

Beyond that, I realize there are probably ways to get rid of the
equality lemmas, but I'm curious how I can make use of
``same_length``. I've seen cases of matching on equality proofs before
to get the typer to unify types...I tried that here but it didn't seem
to work.
|*)

(*|
Answer
------

There is no way of programming ``irev`` without a cast. This is one of
the many reasons why Coq users generally avoid indexed data types like
this :)

Here is one possibility for writing this function:
|*)

Reset ilist. (* .none *) Reset A. (* .none *)
Require Import Coq.Arith.Arith.

Set Implicit Arguments.
Unset Strict Implicit.

Definition cast {A B: Set} (e: A = B): A -> B :=
  match e with eq_refl => fun x => x end.

Section ilist.
  Variable A: Set.

  Inductive ilist: nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint irev_length i1 i2: nat :=
    match i1 with
    | 0    => i2
    | S i1 => irev_length i1 (S i2)
    end.

  Fixpoint irev_aux i1 i2 (ls: ilist i1): ilist i2 -> ilist (irev_length i1 i2) :=
    match ls with
    | Nil      => fun rev => rev
    | Cons h t => fun rev => irev_aux t (Cons h rev)
    end.

  Fixpoint irev_length_plus i1 i2: irev_length i1 i2 = i1 + i2 :=
    match i1 with
    | 0    => eq_refl
    | S i1 => eq_trans (irev_length_plus i1 (S i2)) (Nat.add_succ_r _ _)
    end.

  Definition irev i (l: ilist i) :=
    cast (f_equal ilist (eq_trans (irev_length_plus i 0) (Nat.add_comm _ _)))
         (irev_aux l Nil).

End ilist.

(*|
If you want to prove anything about ``irev``, the easiest is probably
to convert the indexed lists to normal lists and reasoning about
reversal of normal lists. Fun exercise: try showing that ``irev`` is
its own inverse.
|*)
