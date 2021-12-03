(*|
######################################################################
Proving ``forall x xs ys, subseq (x :: xs) ys -> subseq xs ys`` in Coq
######################################################################

:Link: https://stackoverflow.com/questions/54378236/proving-forall-x-xs-ys-subseq-x-xs-ys-subseq-xs-ys-in-coq
|*)

(*|
Question
********

I have the following definition
|*)
Require Import List. (* .none *)
Import ListNotations. (* .none *)
Inductive subseq : list nat -> list nat -> Prop :=
| empty_subseq : subseq [] []
| add_right : forall y xs ys, subseq xs ys -> subseq xs (y :: ys)
| add_both : forall x y xs ys, subseq xs ys -> subseq (x :: xs) (y :: ys).

(*| Using this, I wish to prove the following lemma |*)

Lemma del_l_preserves_subseq : forall x xs ys,
    subseq (x :: xs) ys -> subseq xs ys.

(*|
So, I tried looking at the proof of ``subseq (x :: xs) ys`` by doing
``destruct H``.
|*)

Proof.
  intros. induction H. (* .unfold *)
Abort. (* .none *)

(*|
Why does the first subgoal ask me to prove ``subseq xs []``? Shouldn't
the ``destruct`` tactic know that the proof cannot be of the form
``empty_subseq`` since the type contains ``x :: xs`` and not ``[]``?

In general how do I prove the lemma that I am trying to prove?
|*)

(*|
Answer (Li-yao Xia)
*******************

    Shouldn't the ``destruct`` tactic know that the proof cannot be of
    the form ``empty_subseq`` since the type contains ``x :: xs`` and
    not ``[]``?

In fact, ``destruct`` doesn't know that much. It just replaces ``x ::
xs`` and ``xs`` with ``[]`` and ``[]`` in the ``empty_subseq`` case.
In particular, this frequently leads to lost information in the
context. Better alternatives:

- Use ``inversion`` instead of ``destruct``.
- Use ``remember`` to ensure both type indices of ``subseq`` are
  variables before ``destruct``. (``remember (x :: xs) as xxs in H.``)
  This more explicit goal management also works well with
  ``induction``.
|*)

(*|
Answer (Agnishom Chattopadhyay)
*******************************

Li-yao's answer was actually useful. This is a proof of the lemma.
|*)

Lemma del_l_preserves_subseq : forall x xs ys,
    subseq (x :: xs) ys -> subseq xs ys.
Proof.
  intros x xs ys. induction ys as [|y ys'].
  - intros. inversion H.
  (* Inversion will detect that no constructor matches the type of H *)
  - intros. inversion H.
    (* Inversion will automatically discharge the first case *)
    + (* When [subseq (x :: xs) ys'] holds *)
      apply IHys' in H2. now apply add_right.
    + (* When [subseq xs ys'] holds *)
      now apply add_right.
Qed.
