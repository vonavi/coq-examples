(*|
Closing a lemma on list of nats
===============================

:Link: https://stackoverflow.com/questions/59747670/closing-a-lemma-on-list-of-nats
|*)

(*|
Question
--------

I am stuck to prove the following admitted lemma. Kindly help me how
to proceed.

The function ``sumoneseq`` adds to and returns list of repetitions of
``true``, in reverse order. Given [\ **true**;false;\ **true**;\
**true**;false;\ **true**;\ **true**;\ **true**], it returns [3;2;1].
The function ``sumones`` adds values in the nat list. Given [3;2;1],
it returns 6.
|*)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint sumoneseq (lb: list bool) (ln: list nat) : list nat :=
  match lb, ln with
  | nil, 0::tl'' => tl''
  | nil, _ => ln
  | true::tl', nil => sumoneseq tl' (1::nil)
  | true::tl', h::tl'' => sumoneseq tl' (S h::tl'')
  | false::tl', 0::tl'' => sumoneseq tl' ln
  | false::tl', _ => sumoneseq tl' (0::ln)
  end.

Fixpoint sumones (ln: list nat) : nat :=
  match ln with
  | nil => 0
  | r::tl => r + (sumones tl)
  end.

Lemma sumones_l: forall lb ln,
    sumones (sumoneseq lb ln) = sumones ln + sumones (sumoneseq lb []).
Proof.
  induction ln.
  + simpl. auto.
  + simpl.
Admitted.

(*|
Answer
------

Two things:

1. When proving a property of some function ``f`` using a direct
   induction, choose the parameter on which ``f`` is structurally
   recursive on. So in your example involving ``sumoneseq``, induct on
   ``lb`` instead of ``ln`` since ``sumoneseq`` is structurally
   recursive on ``lb``.
2. Proving a property of some function ``f`` where one or more of its
   arguments are fixed to specific values (e.g. ``sumoneseq`` with its
   second argument being ``[]``) by direct induction is almost
   guaranteed to fail, since the value of that argument varies between
   recursive calls of ``f``, meaning that you would not be able to
   apply the induction hypothesis in your inductive case. In that
   case, you need to manually generalize the induction hypothesis by
   finding a more general property on which ``f`` holds, with each of
   its arguments being sufficiently general. For example, instead of
   proving ``forall lb ln, sumones (sumoneseq lb ln) = sumones ln +
   sumones (sumoneseq lb [])`` directly by induction, try generalizing
   it to something like ``forall lb ln ln', sumones (sumoneseq lb (ln
   ++ ln')) = sumones ln + sumones (sumoneseq lb ln')`` instead and
   prove *that* by direct induction. Your desired result then follows
   as a corollary of that more general result.

You can learn more about generalizing the induction hypothesis in
`James Wilcox's blog post
<https://jamesrwilcox.com/InductionExercises.html>`_ which generously
includes 8 exercises of increasing difficulty on doing just that.

Now try to prove your lemma with these two points in mind. *Hint: when
proving your more general statement about* ``sumoneseq`` *by direct
induction, you may also find it helpful to extract out a suitable
lemma on a certain property of* ``sumones``.

If you've tried again to no avail then the full solution is provided
below the horizontal rule (**spoiler alert!**).

----

Here goes the full solution. As you can probably see, a lot of case
analysis is required on top of the main induction (likely due to your
optimization in ``sumoneseq`` of discarding ``0``'s from ``ln``) and
the reasoning for many of these cases are actually very similar and
repetitive. I could've probably further shortened the proof script
with a bit of ``Ltac`` programming looking for similar patterns in the
various cases but I haven't bothered doing so since I just hacked it
up straight away.
|*)

Reset sumoneseq. (* .none *)
From Coq Require Import List Lia.
Import ListNotations.

Fixpoint sumoneseq (lb: list bool) (ln: list nat) : list nat :=
  match lb, ln with
  | nil, 0::tl'' => tl''
  | nil, _ => ln
  | true::tl', nil => sumoneseq tl' (1::nil)
  | true::tl', h::tl'' => sumoneseq tl' (S h::tl'')
  | false::tl', 0::tl'' => sumoneseq tl' ln
  | false::tl', _ => sumoneseq tl' (0::ln)
  end.

Fixpoint sumones (ln: list nat) : nat :=
  match ln with
  | nil => 0
  | r::tl => r + (sumones tl)
  end.

Lemma sumones_app_plus_distr : forall l l',
    sumones (l ++ l') = sumones l + sumones l'.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl; lia.
Qed.

Lemma sumones_l' : forall lb ln ln',
    sumones (sumoneseq lb (ln ++ ln')) =
    sumones ln + sumones (sumoneseq lb ln').
Proof.
  induction lb; simpl; intros.
  - destruct ln, ln'; simpl; auto.
    + destruct n; rewrite app_nil_r; simpl; auto.
    + destruct n, n0; simpl; rewrite sumones_app_plus_distr;
        simpl; lia.
  - destruct a, ln, ln'; simpl; auto.
    + replace (S n :: ln ++ []) with ((S n :: ln) ++ [])
        by reflexivity.
      replace [1] with ([1] ++ []) by now rewrite app_nil_r.
      repeat rewrite IHlb; simpl; lia.
    + replace (S n :: ln ++ n0 :: ln')
        with ((S n :: ln ++ [n0]) ++ ln')
        by (simpl; now rewrite <- app_assoc).
      replace (S n0 :: ln') with ([S n0] ++ ln')
        by reflexivity.
      repeat rewrite IHlb.
      replace (S n :: ln ++ [n0])
        with ((S n :: ln) ++ [n0])
        by reflexivity.
      repeat rewrite sumones_app_plus_distr; simpl; lia.
    + destruct n.
      * replace (0 :: ln ++ []) with ((0 :: ln) ++ [])
          by reflexivity.
        replace [0] with ([0] ++ [])
          by now rewrite app_nil_r.
        repeat rewrite IHlb; simpl; lia.
      * replace (0 :: S n :: ln ++ [])
          with ((0 :: S n :: ln) ++ []) by reflexivity.
        replace [0] with ([0] ++ [])
          by now rewrite app_nil_r.
        repeat rewrite IHlb; simpl; lia.
    + destruct n, n0.
      * replace (0 :: ln ++ 0 :: ln')
          with ((0 :: ln ++ [0]) ++ ln')
          by (simpl; now rewrite <- app_assoc).
        replace (0 :: ln') with ([0] ++ ln') by reflexivity.
        repeat rewrite IHlb.
        repeat (repeat rewrite sumones_app_plus_distr;
                simpl); lia.
      * replace (0 :: ln ++ S n0 :: ln')
          with ((0 :: ln ++ [S n0]) ++ ln')
          by (simpl; now rewrite <- app_assoc).
        replace (0 :: S n0 :: ln') with ([0; S n0] ++ ln')
          by reflexivity.
        repeat rewrite IHlb.
        repeat (repeat rewrite sumones_app_plus_distr;
                simpl); lia.
      * replace (0 :: S n :: ln ++ 0 :: ln')
          with ((0 :: S n :: ln ++ [0]) ++ ln')
          by (simpl; now rewrite <- app_assoc).
        replace (0 :: ln') with ([0] ++ ln')
          by reflexivity.
        repeat rewrite IHlb.
        repeat (repeat rewrite sumones_app_plus_distr;
                simpl); lia.
      * replace (0 :: S n :: ln ++ S n0 :: ln')
          with ((0 :: S n :: ln ++ [S n0]) ++ ln')
          by (simpl; now rewrite <- app_assoc).
        replace (0 :: S n0 :: ln') with ([0; S n0] ++ ln')
          by reflexivity.
        repeat rewrite IHlb.
        repeat (repeat rewrite sumones_app_plus_distr;
                simpl); lia.
Qed.

Lemma sumones_l: forall lb ln,
    sumones (sumoneseq lb ln) =
    sumones ln + sumones (sumoneseq lb []).
Proof.
  intros; replace (sumoneseq lb ln)
            with (sumoneseq lb (ln ++ []))
    by (now rewrite app_nil_r); apply sumones_l'.
Qed.
