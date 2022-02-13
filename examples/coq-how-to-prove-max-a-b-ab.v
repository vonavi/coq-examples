(*|
#######################################
Coq: How to prove ``max a b <= a + b``?
#######################################

:Link: https://stackoverflow.com/q/46410116
|*)

(*|
Question (re3el)
****************

I am unable to prove the simple logic ``max a b <= a + b`` using coq's
tactics. How should I go about solving it? Below is the code that I
worked on till now. ``s_le_n`` is proved but not mentioned here for
the sake of simplicity.
|*)

Theorem s_le_n: forall (a b: nat),  a <= b -> S a <= S b.
Proof. Admitted.

Theorem max_sum: forall (a b: nat), max a b <= a + b.
Proof.
  intros. induction a.
  - simpl. apply le_n.
  - rewrite plus_Sn_m. induction b.
    + simpl. rewrite <- plus_n_O. apply le_n.
    + rewrite <- plus_Sn_m. simpl. apply s_le_n. Fail rewrite IHa. (* .fails *)
Abort. (* .none *)

(*|
----

**Q (ejgallego):** The proof is less than 40 characters using the
library, I could post it; however, let me ask you something, how would
you prove this lemma using pen and paper?

**A (re3el):** @ejgallego ``if (a > b) then max a b = a, a < a + b;
else max a b = b, b < a + b``. I am unable to use this logic in coq.

|*)

(*|
Answer (ejgallego)
******************

Taking into account @re3el comment, we start from their "pen and paper
proof":

.. code::

    if (a > b) then max a b = a, a < a + b; else max a b = b, b < a + b

Let's now translate that into Coq! In fact, the first thing we need to
do is case on the decidability of ``<``, this is done using the
``le_lt_dec a b`` lemma. The rest is routine:
|*)

Require Import Arith.

Theorem max_sum (a b: nat) : max a b <= a + b.
Proof.
  case (le_lt_dec a b).
  + now rewrite <- Nat.max_r_iff; intros ->; apply le_plus_r.
  + intros ha; apply Nat.lt_le_incl, Nat.max_l_iff in ha.
    now rewrite ha; apply le_plus_l.
Qed.

(*|
However, we can improve this proof quite a bit. There are various
candidates, a good one using the stdlib is:
|*)

Theorem max_sum_1 (a b: nat) : max a b <= a + b.
Proof.
  now rewrite Nat.max_lub_iff; split; [apply le_plus_l | apply le_plus_r].
Qed.

(*|
Using my library of choice [math-comp], you can chain the rewrites to
get a more compact proof:
|*)

From mathcomp Require Import all_ssreflect.

Theorem max_sum_2 (a b: nat) : maxn a b <= a + b.
Proof. by rewrite geq_max leq_addl leq_addr. Qed.

(*|
In fact, on the light of short proof, maybe the original lemma was not
even needed in the first place.

edit: @Jason Gross mentions another style of proof a more seasoned
used would use:

.. coq:: none
|*)

Reset Initial.
Require Import Lia.

Theorem max_sum (a b: nat) : max a b <= a + b.

(*||*)

Proof. apply Max.max_case_strong; lia. Qed.

(*|
However, this proof involves the use of a heavyweight automation
tactic, ``lia``; I strongly advise all beginners to avoid such tactics
for a while, and learn how to do proofs more "manually". In fact,
using any of the SMT-enabled tactics, the original goal can be simply
solved with a call to a SMT.

----

**A (Jason Gross):** There's also a short proof without ssr: ``Require
Import Lia. apply Max.max_case_strong; lia``. It might be nice to
mention this in the answer.

**A (ejgallego):** Thanks Jason; I tend to prefer not to teach ``lia``
and other automated tactics to beginners, IMHO it is very important
that they learn how to do proofs without automation first.
|*)
