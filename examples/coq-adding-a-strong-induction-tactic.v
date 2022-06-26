(*|
#######################################
Coq: adding a "strong induction" tactic
#######################################

:Link: https://stackoverflow.com/q/20883855
|*)

(*|
Question
********

"Strong" (or "complete") induction on the natural number means that
when proving the induction step on ``n``, you can assume the property
holds for any ``k``
|*)

Require Import PeanoNat. (* .none *)
Theorem strong_induction :
  forall P : nat -> Prop,
    (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
    forall n : nat, P n.

(*| .. coq:: none |*)

Proof.
  intros P H n. induction n; apply H; intros k H0.
  - contradiction (Nat.nlt_0_r k).
  - rewrite Nat.lt_succ_r, Nat.le_lteq in H0. destruct H0.
    + clear IHn. revert k H0. induction n; intros k H0.
      * contradiction (Nat.nlt_0_r k).
      * rewrite Nat.lt_succ_r, Nat.le_lteq in H0. destruct H0.
        -- exact (IHn _ H0).
        -- subst k. exact (H _ IHn).
    + now subst k.
Qed.

(*|
I have managed to prove this theorem without too many difficulties.
Now I want to use it in a new tactic, ``strong_induction``, which
should be similar to the standard ``induction n`` technique on the
natural numbers. Recall that when using ``induction n`` when ``n`` is
a natural number and the goal is ``P(n)``, we get two goals: one of
the form ``P(0)`` and the second of the form ``P(S(n))``, where for
the second goal we get ``P(n)`` as assumption.

So I want, when the current goal is ``P(n)``, to get one new goal,
also ``P(n)``, but the new assumption ``forall k : nat, (k < n ->
P(k)))``.

The problem is I don't know how to do it technically. My main problem
is this: suppose ``P`` is a complex statement, i.e.

.. coq:: none
|*)

Goal forall a b, exists q r : nat, a = b * q + r.
  intros a b.

(*||*)

  Show. (* .unfold .goals *)

(*|
with ``a b : nat`` in the context; how can I tell Coq to do the strong
induction on ``a`` and not on ``b``? Simply doing ``apply
strong_induction`` results in
|*)

  apply strong_induction; intros. (* .none *)
  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
where the assumption is useless (since ``n`` does not relate to ``a``)
and I have no idea what the second goal means.
|*)

(*|
Answer
******

In this case, to ``apply strong_induction`` you need to ``change`` the
conclusion of the goal so that it better matches the conclusion of the
theorem.
|*)

Goal forall a b, b <> 0 -> exists ! q r, a = q * b + r /\ r < b.
  change (forall a, (fun c => forall b,
                         b <> 0 -> exists ! q r, c = q * b + r /\ r < b) a).
  eapply strong_induction.
Abort. (* .none *)

(*|
You could also use more directly the ``refine`` tactic. This tactic is
similar to the ``apply`` tactic.
|*)

Goal forall a b, b <> 0 -> exists ! q r, a = q * b + r /\ r < b.
  refine (strong_induction _ _).
Abort. (* .none *)

(*|
But the ``induction`` tactic already handles arbitrary induction
principles.
|*)

Goal forall a b, b <> 0 -> exists ! q r, a = q * b + r /\ r < b.
  induction a using strong_induction.

(*|
More on these tactics `here
<http://coq.inria.fr/refman/tactic-index.html>`__. You should probably
use ``induction`` before ``intro``-ing and ``split``-ing.

----

**Q:** ``induction a using strong_induction`` works great! On the
other hand, the ``change`` tactic fails with "Error: Not convertible."

**A:** when the change is too complex, you can try with the
``replace`` tactic, which will ask for a proof of equality. ``change``
is just ``replace`` when the proof is trivially reflexivity.
|*)
