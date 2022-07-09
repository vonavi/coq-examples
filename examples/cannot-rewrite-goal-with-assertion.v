(*|
###################################
Cannot rewrite goal with assertion?
###################################

:Link: https://stackoverflow.com/q/70490662
|*)

(*|
Question
********

I am not sure I understand why in some cases rewriting ``H`` works,
and in some it doesnt. Here for example:
|*)

Require Import PeanoNat.

Theorem add_assoc2 : forall n m : nat, n + m = m + n.
Proof. intros. rewrite Nat.add_comm. reflexivity. Qed.

Theorem plus_4 : forall n m p q : nat,
    n + (n * p) + m + (m * p) = n + m + (n * p) + (m * p).
Proof.
  intros.
  assert (H : n * p + m = m + n * p).
  { rewrite <- add_assoc2. reflexivity. }
  Fail rewrite H. (* .fails *)

(*| Gives: |*)

  Show. (* .unfold .messages *)

(*| But Coq complains: |*)

  Fail rewrite H. (* .unfold .messages *)
Abort. (* .none *)

(*|
I clearly see one, on the left side. When using induction, rewriting
with ``IHn`` doesn't pose any problem, even if there are some other
terms in front of rewriteable expression.
|*)

(*|
Answer
******

You can "see" a subterm ``n * p + m``, but this is misleading: Coq
doesn't show you the implicit parentheses around all the ``+``
expressions.

Use
|*)

Set Printing Parentheses.

(*|
to make them visible. Your proof state is really:

.. coq:: none
|*)

Theorem plus_4 : forall n m p q : nat,
    n + (n * p) + m + (m * p) = n + m + (n * p) + (m * p).
Proof.
  intros.
  assert (H : n * p + m = m + n * p).
  { rewrite <- add_assoc2. reflexivity. }

(*||*)

  Show. (* .unfold .messages *)

(*|
Coq was right that there is no subterm that matches ``H``'s left hand
side expression ``((n * p) + m)``. You need to rewrite using some
associativity lemmas to shift the parentheses around.

Also, ``add_assoc2`` is not a good name for a lemma ``forall n m :
nat, n + m = m + n``. This is a **commutativity** property, not
associativity.
|*)
