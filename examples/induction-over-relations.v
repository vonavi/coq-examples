(*|
########################
Induction over relations
########################

:Link: https://stackoverflow.com/q/44024840
|*)

(*|
Question
********

I'm trying to prove the following toy theorem about the ordering of
the naturals:
|*)

Inductive Le : nat -> nat -> Prop :=
| le_n : forall n, Le n n
| le_S : forall n m, Le n m -> Le n (S m).

Theorem le_Sn_m : forall n m, Le (S n) m -> Le n m.

(*|
On paper, this is a simple induction on ``Le (S n) m``. In particular,
the base case of ``le_n`` is trivial.

In Coq though, beginning my proof with induction gives me the
following:
|*)

Proof.
  intros n m H. induction H. Show. (* .unfold .messages *)
Abort. (* .none *)

(*| How should I proceed instead? |*)

(*|
Answer (Vinz)
*************

This is due to a limitation of Coq, when using ``induction`` on term
that are not made only of variables. By doing your induction, Coq
forgets about the fact that the first argument was a ``S`` of some
``n``.

You can do the following instead:
|*)

Theorem le_Sn_m_ : forall X m, Le X m -> forall n, X = S n -> Le n m.
Abort. (* .none *)

(*|
I think there is a ``dependent induction`` somewhere that could save
you this intermediate lemma but I can't recall where.
|*)

(*|
Answer (Zimm i48)
*****************

Similar to @Vinz suggestion, but without changing the statement you
are proving:
|*)

Theorem le_Sn_m : forall n m, Le (S n) m -> Le n m.
Proof.
  intros n m H. remember (S n) as p. induction H; subst n0.
  - do 2 constructor.
  - constructor. now apply IHLe.
Qed.

(*|
Using the `remember
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.remember>`__
tactic will introduce an equality in your context which will avoid
losing this critical information.
|*)

(*|
Answer (Anton Trunov)
*********************

This is happening because Coq treats differently *indices* and
*parameters* (see the accepted answer to `this question
<https://stackoverflow.com/q/24600256/2747511>`__ for a very nice
explanation). Your ``Le`` relation uses indices only, whereas the
standard definition makes the first argument a parameter:
|*)

Print le. (* .unfold .messages *)

(*|
I can recommend reading `this blog post
<https://homes.cs.washington.edu/~jrw12/dep-destruct.html>`__ by James
Wilcox. Here is a relevant excerpt:

    When Coq performs a case analysis, it first abstracts over all
    indices. You may have seen this manifest as a loss of information
    when using destruct on predicates

So you can either (1) change your ``Le`` relation so it would use a
parameter, or (2) use the ``remember`` tactic as was suggested by
@Zimm i48, or (3) use the ``dependent induction`` tactic mentioned by
@Vinz:
|*)

Reset Initial. (* .none *)
Require Import Coq.Program.Equality. (* for `dependent induction` *)

Inductive Le : nat -> nat -> Prop :=
| le_n : forall n, Le n n
| le_S : forall n m, Le n m -> Le n (S m).
Hint Constructors Le. (* so `auto` will work *)

Theorem le_Sn_m : forall n m, Le (S n) m -> Le n m.
Proof.
  intros n m H. dependent induction H; auto.
Qed.
