(*|
#####################
Coq auto tactic fails
#####################

:Link: https://stackoverflow.com/questions/61677391/coq-auto-tacitc-fails
|*)

(*|
Question
********

I have the following Coq program that tries to prove ``n <= 2^n`` with
``auto``:
|*)

(***********)
(* imports *)
(***********)
Require Import Nat.

(************************)
(* exponential function *)
(************************)
Definition f (a : nat) : nat := 2^a.

Hint Resolve plus_n_O.
Hint Resolve plus_n_Sm.

(**********************)
(* inequality theorem *)
(**********************)
Theorem a_leq_pow_2_a: forall a, a <= f(a).
Proof.
  auto with *.

(*|
I expected Coq to either succeed or get stuck trying to. But it
immediately returns. What am I doing wrong?

**EDIT** I added the ``Hint Unfold f.``, and increased bound to 100
but I can't see any unfolding done with ``debug auto 100``:
|*)

  (* debug auto: *)
  * Fail assumption. (* .fails *) (*fail*) Restart. (* .none *)

  * intro. (*success*)
    Fail assumption. (* .fails *) (*fail*) Undo. (* .none *)

    Fail intro. (* .fails *) (*fail*) Undo. (* .none *)

    Fail simple apply le_n. (* .fails *) (*fail*) Undo. (* .none *)

    Fail simple apply le_S. (* .fails *) (*fail*)
Abort. (* .none *)

(*|
**EDIT 2** I'm adding the manual proof to demonstrate its complexity:
|*)

Require Import PeanoNat. (* .none *)
(**********************)
(* inequality theorem *)
(**********************)
Theorem a_leq_pow_2_a: forall a, a <= f(a).
Proof.
  induction a as [|a' IHa].
  - apply le_0_n.
  - unfold f.
    rewrite Nat.pow_succ_r.
    + rewrite Nat.mul_comm.
      rewrite Nat.mul_succ_r.
      rewrite Nat.mul_1_r.
      unfold f in IHa.
      rewrite Nat.add_le_mono with (n:=1) (m:=2^a') (p:=a') (q:=2^a').
      * reflexivity.
      * apply Nat.pow_le_mono_r with (a:=2) (b:=0) (c:=a').
        auto. apply le_0_n.
      * apply IHa.
    + apply le_0_n.
Qed.

(*|
Answer (Yves)
*************

The manual proof that you performed explains why ``auto`` can't do it.
You did a proof by induction and then a few rewrites. The ``auto``
tactic does not allow itself this kind of step.

The tactic ``auto`` is meant to find a proof if a manual proof only
uses ``apply`` with a restricted set of theorems. Here the restrict
set of theorems is taken from the ``core`` hint database. For the sake
of brevity, let's assume this database only contains ``le_S``,
``le_n``, ``plus_n_O`` and ``plus_n_Sm``.

To simplify, let's assume that we work with the goal ``a <= 2 ^ a``.
The head predicate of this statement is ``_ <= _`` so the tactic will
only look at theorems whose principal statement is expressed with ``_
<= _``. This rules out ``plus_n_O`` and ``plus_n_Sm``. Your initiative
of adding these goes down the drain.

If we look at ``le_n`` the statement is ``forall n : nat, n <= n``. If
we replace the universal quantification by a *pattern variable*, this
pattern is ``?1 < ?1``. Does this unify with ``a <= 2 ^ a``? The
answer is no. so this theorem won't be used by ``auto``. Now if we
look at ``le_S``, the pattern of the principal statement is ``?1 <= S
?2``. Unifying this pattern with ``a <= 2 ^ a``, this would require
``?1`` to be ``a``. Now what could be the value of ``?2``? We need to
compare symbolically the expressions ``2 ^ a`` and ``S ?2``. On the
left hand side the function symbol is either ``_ ^ _`` or ``2 ^ _``
depending on how you wish to look at it, but anyway this is not ``S``.
So ``auto`` recognizes these functions are not the same, the lemma
cannot apply. ``auto`` fails.

I repeat: when given a goal, ``auto`` first only looks at the head
symbol of the goal, and it selects from its database the theorems that
achieves proofs for this head symbol. In your example, the head symbol
is ``_ <= _``. Then it looks only at the conclusion of these theorems,
and checks whether the conclusion matches syntactically with the goal
at hand. If it does match, then this should provide values for the
universally quantified variables of the theorem, and the premises of
the theorem are new goals that should be solved at a lower depth. As
was mentioned by @Elazar, the depth is limited to 5 by default.

The ``Hint unfold`` directive would be useful only if you had made a
definition of the following shape:
|*)

Definition myle (x y : nat) := x <= y.

(*|
Then ``Hint Unfold myle : core.`` would be useful to make sure that
the database theorems for ``_ <= _`` are also used to proved instances
of ``myle``, as in the following example (it fails if we have 4
occurrences of ``S``, because of the depth limitation).
|*)

Hint Unfold myle : core. (* .none *)
Lemma myle3 (x : nat) : myle x (S (S (S x))).
Proof. auto with core. Qed.

(*|
Please note that the following statement is logically equivalent
(according to the definition of addition) but not provable by
``auto``. Even if you add ``Hint Unfold plus : core.`` as a directive,
this won't help because ``plus`` is not the head symbol of the goal.
|*)

Hint Unfold plus : core. (* .none *)
Lemma myleplus3 (x : nat) : myle x (3 + x).
Proof.
  auto. (* the goal is unchanged. *)
  simpl. auto.
Qed.

(*|
I often use automatic tactics from Coq, for instance ``lia``, but I
always do so because I can predict if the goal is part of the intended
scope of the tactic.
|*)

(*|
Answer (Elazar)
***************

From the `documentation
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.auto>`_:

    This tactic implements a Prolog-like resolution procedure to solve
    the current goal. It first tries to solve the goal using the
    assumption tactic, then it reduces the goal to an atomic one using
    intros and introduces the newly generated hypotheses as hints.
    Then it looks at the list of tactics associated to the head symbol
    of the goal and tries to apply one of them (starting from the
    tactics with lower cost). This process is recursively applied to
    the generated subgoals.

Also, see the warning there:

    ``auto`` uses a weaker version of apply that is closer to simple
    apply so it is expected that sometimes auto will fail even if
    applying manually one of the hints would succeed.

And finally, the search depth is limited to 5 by default; you can
control it using ``auto num``.

So if at any point, none of the "tactics associated to the head
symbol" of the current goal makes any progress, ``auto`` will fail.
And if ``auto`` reaches maximum depth, it will fail.

Note that ``auto`` it does not automatically apply the ``unfold``
tactic. There's no way to solve ``a <= f(a)`` when ``f`` is opaque,
without further assumptions. If you want, you can use `Hint Unfold f
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:cmdv.hint-unfold>`_
or `Hint Transparent f
<https://coq.inria.fr/refman/proof-engine/tactics.html#coq:cmdv.hint-transparent>`_.
|*)
