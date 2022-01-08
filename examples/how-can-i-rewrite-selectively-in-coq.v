(*|
#####################################
How can I rewrite selectively in Coq?
#####################################

:Link: https://stackoverflow.com/q/47940841
|*)

(*|
Question
********
|*)

Require Import Coq.Arith.Arith.

Section foo.

  Variable a : nat.
  Variable fvs : list nat.
  Variable maxNum : list nat -> nat.
  Hypothesis H : a = max (maxNum fvs) a + 1.
  Hypothesis H1 : max (maxNum fvs) a >= a.

  Goal False. (* .unfold *)

(*|
Doing ``rewrite H in H1.``, replaces both the ``a``\ s whereas I only
want to rewrite the ``a`` on the RHS. Can it be done? I want to prove
false from the above two hypotheses.
|*)

(*|
Answer
******

One option is to use ``rewrite ... at <position>.`` like so:
|*)

    rewrite H in H1 at 2.

(*|
What you want can also be done in a slightly different way. Observe
that ``max (maxNum fvs) a`` is irrelevant here -- you can use any
natural number instead of that expression and your theorem would still
hold. That means you can use the ``generalize`` tactic.
|*)

    Undo.
    revert H H1. generalize (max (maxNum fvs) a) as n.
    intros n ->. rewrite Nat.add_1_r.
    apply Nat.nle_succ_diag_l.
  Qed.

End foo.
