(*|
######################################
Using induction starting from 1 in Coq
######################################

:Link: https://stackoverflow.com/questions/54752428/using-induction-starting-from-1-in-coq
|*)

(*|
Question
********

I am trying to use induction starting from 1 in a Coq proof. From
`this question
<https://stackoverflow.com/questions/27205573/coq-induction-start-at-specific-nat>`__
I got a proof of the induction principle I need:
|*)

Require Import Coq.micromega.Lia.

Section induction_at_1.
  Variable P : nat -> Prop.
  Hypothesis p1 : P 1.
  Hypothesis pS : forall n, P n -> P (S n).

  Theorem induction_at_1:
    forall n, n > 0 -> P n.
  Proof using p1 pS.
    induction n; intro.
    - exfalso. lia.
    - destruct n.
      + apply p1.
      + assert (S n > 0) by lia. intuition.
  Qed.
End induction_at_1.

(*|
What I get looks structurally very similar to standard induction. In
fact, ``Check nat_ind`` yields
|*)

Check nat_ind. (* .unfold .messages *)

(*| while ``Check induction_at_1`` yields *)

Check induction_at_1. (* .unfold .messages *)

(*|
The issue arises when I try to apply this induction principle. For
instance, I would like to prove by induction
|*)

Lemma cancellation:
  forall a b c : nat, a > 0 -> a * b = a * c -> b = c.

(*|
This seems exactly suited to the kind of induction I have above, but
when I start my proof like this
|*)

  intros a b c H0 H1.
  Fail induction a using induction_at_1. (* .unfold .fails .in .messages *)
Abort. (* .none *)

(*|
I get the above error, which I cannot interpret. Since the two
induction principles look almost identical to me, I am not sure why
this does not work. Any ideas?
|*)

(*|
Answer
******

I also find this behavior puzzling, but there are a few ways around
it. One is to use the ssreflect induction tactic, called ``elim``:
|*)

From Coq Require Import ssreflect.

Lemma cancellation:
  forall a b c : nat, a > 0 -> a * b = a * c -> b = c.
Proof.
  intros a b c H.
  elim/induction_at_1: a / H.
  (* ... *)
Abort.

(*|
The second line is telling Coq to perform induction on ``H`` (not
``a``) while generalizing ``a`` and using the induction principle
``induction_at_1``. I couldn't get something similar to work using the
regular Coq ``induction``.

An alternative is to use plain natural number induction. In this case,
I believe that the lemma follows by induction on ``b`` while
generalizing ``c`` (I am not sure that induction on ``a`` works). If
you do need to show something of the form ``m <= n -> P n`` for all
``n``, you can replace ``n`` by ``n - m + m`` (which should be
possible with the ``m <= n`` hypothesis), and then prove ``P (n - m +
m)`` by induction on ``n - m``.
|*)
