(*|
##################################################################################################################################################
How to write intermediate proof statements inside Coq - similar to how in Isar one has ``have Statement using Lemma1, Lemma2 by auto`` but in Coq?
##################################################################################################################################################

:Link: https://stackoverflow.com/q/70324745
|*)

(*|
Question
********

I wanted to write intermediate lemmas inside Coq proof scripts, e.g.,
inside SCRIPT in ``Proof. SCRIPT Qed.`` itself - similar to how one
would do in Isar. How does one do this in Coq? e.g.:

.. code-block:: isabelle

    have Lemma using Lemma1, Lemma2 by auto.

I am aware of the ``exact`` statement and wonder if that is it... but
I'd like to have the proof for the statement too like in Isar we have
``have by auto`` or ``using Proof. LEMMA_PROOF Qed.``

To make it concrete, I was trying to do these very simple proofs:
|*)

Module small_example.

Theorem add_easy_induct_1 : forall n : nat, n + 0 = n.
Proof.
  intros. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros. induction n as [| n' IH].
  - simpl. rewrite -> add_easy_induct_1. reflexivity.
  - simpl. rewrite -> IH. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

End small_example.

(*|
but I wasn't sure how and it wasn't working too well.

----

I'm also interested in ``shows`` in Coq e.g.

.. code-block:: isabelle

    shows T using lemmas by hammer.

Current answers are good in showing that the have and by statements
exist in Coq. However, what is crucially missing is 1) the ``shows``
statement and 2) the ``using`` statements. I'd like to see similar
constructs with those in Coq proofs -- especially the using one that
works with ``shows``'s and ``have``'s.

----

What Isabelle seems to be good at is declaring statements as true
given a proof and a list of hypothesis. So for example ``have name: L
using l1 by metis.`` would create the ``lemma L`` as a new fact, give
it name ``name`` but prove it using the tactic ``metis`` but crucially
depending on the fact ``l1`` as something given for that statement to
succeed. So I want to be able to declare things and be checked by a
tactic/ATP in Coq.

----

Related:

- I am aware of Czar
  (https://coq.discourse.group/t/what-is-the-difference-between-ssreflect-and-czar/824)
  but that is no longer supported in Coq afaik.
|*)

(*|
Answer (Li-yao Xia)
*******************

You can write ``assert <lem>`` to prove an intermediate result
``<lem>`` in the middle of a proof. Other variants are ``assert <lem>
by <tactic>`` to immediately prove ``<lem>`` using ``<tactic>``, or
``assert (<lemname> : <lem>)`` to give a name to the lemma. Example:
|*)

Reset Initial. (* .none *)
Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros. induction n as [| n' IH].
  - simpl.
    assert (add_easy_induct_1 : forall n, n + 0 = n) by (induction n; auto).
    rewrite -> add_easy_induct_1. reflexivity.
  - simpl.
    assert (plus_n_Sm : forall n m, S (n + m) = n + S m) by (induction n; auto).
    rewrite -> IH. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

(*|
Documentation on ``assert``:
https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#coq:tacn.assert
|*)

(*|
Answer (Pierre Jouvelot)
************************

You can use the ``have:`` construct in the ``ssreflect`` language of
tactics for Coq, with pretty much the same semantics you want, plus a
couple of additional nice features related to how this lemma can be
used right away (e.g., for rewriting) instead of being given a name.

For a concrete code example, see
https://stackoverflow.com/a/71428239/1601580
|*)

(*|
Answer (Charlie Parker)
***********************

To provide an example to https://stackoverflow.com/a/70326508/1601580
answer, here is some code example for ``have``:
|*)

Reset Initial. (* .none *)
Theorem n_plus_zero_eq_n : forall n : nat, n + 0 = n.
Proof.
  intros. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem Sn_plus_m_eq_n_plus_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IH].
  - auto.
  - simpl. rewrite <- IH. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros. induction n as [| n' IH].
  - simpl. rewrite -> n_plus_zero_eq_n. reflexivity.
  - simpl. rewrite -> IH. rewrite -> Sn_plus_m_eq_n_plus_Sm. reflexivity.
Qed.

(* have proof *)
From Coq Require Import ssreflect ssrfun ssrbool.

Theorem add_comm_have : forall n m : nat, n + m = m + n.
Proof.
  intros. induction n.
  - simpl.
    have: (forall n, n + 0 = n) by apply n_plus_zero_eq_n.
    move=> H. rewrite -> H. by reflexivity.
  - simpl. rewrite IHn.
    have: (forall n m : nat, S (n + m) = n + (S m))
      by apply Sn_plus_m_eq_n_plus_Sm.
    move=> H'. rewrite -> H'. by reflexivity.
Qed.

(*| second example based on comment: |*)

From Coq Require Import ssreflect ssrfun ssrbool.

Theorem add_comm_have' : forall n m : nat, n + m = m + n.
Proof.
  intros. induction n.
  - simpl.
    have -> //: forall n, n + 0 = n by apply n_plus_zero_eq_n.
  - simpl. rewrite IHn.
    have -> //: forall n m: nat, S (n + m) = n + (S m)
               by apply Sn_plus_m_eq_n_plus_Sm.
Qed.

(*|
----

**A:** If you write ``have -> //: forall n, n + 0 = n by (apply
n_plus_zero_eq_n).``, you don't even need the ``move=> H``, ``rewrite
-> H`` and ``by reflexivity`` (``//`` asks to perform trivial
simplifications).
|*)
