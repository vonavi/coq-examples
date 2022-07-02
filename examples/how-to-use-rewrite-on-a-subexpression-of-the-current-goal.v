(*|
#############################################################
How to use ``rewrite`` on a subexpression of the current goal
#############################################################

:Link: https://stackoverflow.com/q/13645979
|*)

(*|
Question
********

In Coq, is it somehow possible to apply a lemma or hypothesis to a
subexpression of the current goal? For example I would like to apply
the fact that plus is commutative in order to swap 3 and 4 in this
example.
|*)

Require Import Coq.Arith.Plus.

Inductive foobar : nat -> Prop :=
| foob : forall n : nat, foobar n.

Goal foob (3 + 4) = foob (4 + 3).
Proof.
  Fail apply plus_comm. (* .fails *) (* or maybe rewrite plus_comm *)

(*| gives: |*)

  Fail apply plus_comm. (* .unfold .messages *)

(*|
How can I tell Coq where exactly in this goal to ``apply plus_comm``?
|*)

(*|
Answer
******

In this particular case, ``rewrite`` will work if you define the
inductive type using a constructor parameter instead of an index:
|*)

Reset foobar. (* .none *)
Inductive foobar : Type :=
| foob (n : nat).

(*|
Since there is only one constructor for this type, my understanding
(`from this answer
<https://stackoverflow.com/questions/24600256/difference-between-type-parameters-and-indices>`__)
is that using an index does not provide any benefit but makes it
harder for Coq to pattern-match.

In general, either of the following techniques can achieve the effect
of a targeted ``rewrite``:

assert
======
|*)

Goal foob (3 + 4) = foob (4 + 3). (* .none *)
Proof. (* .none *)
  assert (H: 3 + 4 = 4 + 3). { rewrite <- plus_comm. reflexivity. }

(*|
rewrite
=======
|*)

  Restart. (* .none *)
  (* introduce a new sub-goal where you can prove that the replacement is OK *)
  replace (3 + 4) with (4 + 3).
  (* Coq orders the new goal last. I think it's clearer to tackle it first *)
  2: {
    (* do the rewrite *)
    rewrite <- plus_comm. reflexivity.
  }
