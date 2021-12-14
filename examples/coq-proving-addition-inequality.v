(*|
###############################
Coq proving addition inequality
###############################

:Link: https://stackoverflow.com/questions/67177067/coq-proving-addition-inequality
|*)

(*|
Question
********

I am a beginner and trying to prove this lemma:
|*)

Lemma test:  forall n m p q : nat,
    n <= p \/ m <= q -> n + m <= p + q.
Abort. (* .none *)

(*| I tried |*)

Require Import Lia.

Lemma test:  forall n m p q : nat,
    n <= p \/ m <= q -> n + m <= p + q.
Proof.
  Fail intros; lia. (* .fails *)
Abort. (* .none *)

(*| but it is not working. How could I proceed? |*)

(*|
Answer
******

You probably meant
|*)

Lemma test:  forall n m p q : nat,
    n <= p /\ m <= q -> n + m <= p + q.
Abort. (* .none *)

(*|
with ``/\`` (logical and) rather than ``\/`` (logical or) because your
theorem does not hold otherwise. As a counterexample, pick ``n = p = q
= 0`` and ``m = 1``.

When fixed that way, ``lia`` finds the proof automatically.

Also, note it is more idiomatic in Coq to currify types, that is
replacing conjunction on the left of an arrow with an arrow. This
would read
|*)

Lemma test:  forall n m p q : nat,
    n <= p -> m <= q -> n + m <= p + q.
Abort. (* .none *)

(*| which is equivalent. |*)
