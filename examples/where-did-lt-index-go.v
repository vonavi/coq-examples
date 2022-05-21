(*|
##########################
Where did ``lt_index`` go?
##########################

:Link: https://stackoverflow.com/q/38755038
|*)

(*|
Question
********

I was using a lemma named ``lt_index`` in Coq, I remember it states
that

.. code-block:: coq

    n < 2 * m + 1 -> (n - 1) / 2 < m

Now, I can't use this lemma anymore, and when I do ``SearchAbout
lt_index``, coq answers with

    Error: The reference lt_index was not found in the current
    environment.

My imports are as follows
|*)

Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Arith.

(*|
Did I miss something?

EDIT: Apparently, I dreamed about this ``lt_index`` lemma and never
existed. Anyway, I came up with a proof to the same result, I added
``1 <= n`` as precondition. Here it is
|*)

Lemma lt_solve : forall (n m : nat),
    1 <= n -> n < 2 * m + 1 -> (n - 1) / 2 < m.
Proof.
  intros. assert (n <= n - 1 + 1).
  - apply Nat.sub_add_le.
  - inversion H1.
    + rewrite <-H2. rewrite H2 in H0.
      rewrite plus_comm in H0. assert (2 * m + 1 = 1 + 2 * m).
      * apply plus_comm.
      * rewrite H3 in H0. apply plus_lt_reg_l in H0.
        apply Nat.div_lt_upper_bound in H0.
        -- trivial.
        -- discriminate.
    + rewrite plus_comm in H2.
      rewrite (le_plus_minus_r 1 n) in H2.
      * eapply (le_lt_trans n m0 (S m0)) in H3.
        -- rewrite H2 in H3. contradict H3. apply lt_irrefl.
        -- apply lt_n_Sn.
      * trivial.
Qed.

(*|
If you realize there is an improvement to this proof, I'd be glad to
hear about it.
|*)

(*|
Answer (larsr)
**************

While it is good to try to solve these kinds of problems by hand as an
exercise, in the long run it can get tedious, if you really want to
work on something else.

There are tactics that can help you to solve systems of equations with
inequalities. You can for instance use the tactics ``lia`` from
``Psatz``, or ``omega`` from ``Omega``. The proof terms are not a
pretty sight, but if that doesn't matter then why not.

Unfortunately they don't handle division, so they can't solve this
system, but there is a lemma in the library that you can use to get
rid of the ``/``. I found it by doing ``Search ( _ / _ < _ ).``
|*)

Reset Initial. (* .none *)
Require Import Coq.Numbers.Natural.Peano.NPeano.
(* this provides 'lia' for solving linear integer arithmetic *)
Require Import Psatz.

Lemma lt_solve : forall (n m : nat),
    1 <= n -> n < 2 * m + 1 -> (n - 1) / 2 < m.
Proof.
  intros. apply Nat.div_lt_upper_bound; lia.
Qed.

(*|
Answer (Anton Trunov)
*********************

If you for some reason would like to get a "manual" solution, using
the standard library, then here it is.
|*)

Reset Initial. (* .none *)
Require Import Coq.Arith.Arith.

Lemma lt_solve : forall (n m : nat),
    1 <= n -> n < 2 * m + 1 -> (n - 1) / 2 < m.
Proof with auto.
  intros. apply Nat.div_lt_upper_bound... destruct n.
  - inversion H.
  - rewrite Nat.sub_succ, Nat.sub_0_r, (Nat.add_lt_mono_r _ _ 1).
    rewrite Nat.add_1_r...
Qed.

(*|
----

**Q:** Thanks @Anton, one question: why did you add ``Proof with
auto`` at the very beginning of your proof? What is the role of ``with
auto``?

**A:** It's just a shortcut. The construction ``Proof with <tactic>``
works as follows. When you see ellipsis (``...``) ending a tactic t1,
it's equivalent to turning it into ``t1; <tactic>``. So ``rewrite
Nat.add_1_r...`` behaves as ``rewrite Nat.add_1_r; auto``.
|*)
