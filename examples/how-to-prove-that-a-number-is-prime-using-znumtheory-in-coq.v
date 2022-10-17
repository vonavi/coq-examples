(*|
###########################################################
How to prove that a number is prime using Znumtheory in Coq
###########################################################

:Link: https://stackoverflow.com/q/49282773
|*)

(*|
Question
********

I'm trying to prove that a number is prime using the Znumtheory
library.

In Znumtheory primes are defined in terms of relative primes:
|*)

Require Import ZArith Znumtheory. (* .none *)
Inductive prime (p : Z) : Prop :=
  prime_intro :
    1 < p -> (forall n : Z, 1 <= n < p -> rel_prime n p) -> prime p.

(*|
So to prove that ``3`` is prime I should apply ``prime_intro`` to the
goal. Here is my try:
|*)

Require Import Lia.
Theorem prime3 : prime 3.
Proof.
  apply prime_intro.
  - lia.
  - intros. unfold rel_prime. apply Zis_gcd_intro.
    + apply Z.divide_1_l.
    + apply Z.divide_1_l.
    + intros. Abort.

(*|
I don't know how to use the hypothesis ``H : 1 <= n < 3`` which says
that ``n`` is ``1`` or ``2``. I could destruct it, apply
``lt_eq_cases`` and destruct it again, but I would be stuck with a
useless ``1 < n`` in the first case.

I wasn't expecting to have a hard time with something that looks so
simple.
|*)

(*|
Answer (larsr)
**************

Here is a proof that I think is quite understandable as one steps
through it. It stays at the level of number theory and doesn't unfold
definitions that much. I put in some comments, don't know if it makes
it more or less readable. But try to step through it in the IDE, if
you care for it...
|*)

Reset Initial. (* .none *)
Require Import ZArith.
Require Import Znumtheory.

Inductive prime (p : Z) : Prop :=
  prime_intro :
    1 < p -> (forall n : Z, 1 <= n < p -> rel_prime n p) -> prime p.

Require Import Lia.

Theorem prime3 : prime 3.
Proof.
  constructor.
  - lia.                        (* prove 1 < 3 *)
  - intros. constructor.        (* prove rel_prime n 3 *)
    + exists n. lia.            (* prove (1 | n) *)
    + exists 3. lia.            (* prove (1 | 3) *)

      (* our goal is now (x | 1), and we know (x | n) and (x | 3) *)
    + assert (Hn : n = 1 \/ n = 2) by lia. clear H. (* because 1 <= n < 3 *)
      case Hn.                  (* consider cases n=1 and n=2 *)
      * intros. subst.
        (* case n = 1: proves (x | 1) because we know (x | n) *)
        trivial.
      * intros. subst.   (* case n = 2: we know (x | n) and (x | 3) *)
        assert (Hgcd: (x | Z.gcd 2 3)) by (apply Z.gcd_greatest; trivial).
        (* Z.gcd_greatest: (x | 2) -> x | 3) -> (x | Z.gcd 2 3) *)
        apply Hgcd.         (* prove (x | 1), because Z.gcd 2 3 = 1 *)
Qed.

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

The lemma you mentioned is actually proved in that library, under the
name ``prime_3``. You can look up its proof on `GitHub
<https://github.com/coq/coq/blob/master/theories/ZArith/Znumtheory.v>`__.

You mentioned how strange it is to have such a hard time to prove
something so simple. Indeed, the proof in the standard library is
quite complicated. Luckily, there are much better ways to work out
this result. The `Mathematical Components
<https://github.com/math-comp/math-comp>`__ library advocates for a
different style of development based on boolean properties. There,
``prime`` is not an inductively defined predicate, but a function
``nat -> bool`` that checks whether its argument is prime. Because of
this, we can prove such simple facts by computation:
|*)

Set Warnings "-notation-overridden". (* .none *)
From Coq Require Import ssreflect ssrbool.
From mathcomp Require Import ssrnat prime.

Lemma prime_3 : prime 3. Proof. reflexivity. Qed.

(*|
There is a bit of magic going on here: the library declares a coercion
``is_true : bool -> Prop`` that is automatically inserted whenever a
boolean is used in a place where a proposition is expected. It is
defined as follows:
|*)

Definition is_true (b : bool) : Prop := b = true.

(*|
Thus, what ``prime_3`` really is proving above is ``prime 3 = true``,
which is what makes that simple proof possible.

The library allows you to connect this boolean notion of what a prime
number is to a more conventional one via a *reflection lemma*:
|*)

From mathcomp Require Import div eqtype.
Close Scope Z_scope. (* .none *)

Lemma primeP p :
  reflect (p > 1 /\ forall d, d %| p -> xpred2 1 p d) (prime p).

(*|
Unpacking notations and definitions, what this statement says is that
``prime p`` equals ``true`` if and only if ``p > 1`` and every ``d``
that divides ``p`` is equal to ``1`` or ``p``. I am afraid it would be
a lengthy detour to explain how this reflection lemma works exactly,
but if you find this interesting I strongly encourage you to look up
more about Mathematical Components.
|*)

(*|
Answer (epoiner)
****************

I have a variant of @larsr's proof.
|*)

Reset Initial. (* .none *)
Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.

Theorem prime3 : prime 3.
Proof.
  constructor.
  - lia.
  - intros. assert (n = 1 \/ n = 2) as Ha by lia.
    destruct Ha; subst n; apply Zgcd_is_gcd.
Qed.

(*|
Like @larsr's proof, we prove that ``1 < 3`` using ``lia`` and then
prove that either ``n = 1`` or ``n = 2`` using ``lia`` again.

To prove ``rel_prime 1 3`` and ``rel_prime 2 3`` which are defined in
terms of ``Zis_gcd``, we apply ``Zgcd_is_gcd``. This lemma states that
computing the ``gcd`` is enough. This is trivial on concrete inputs
like ``(1, 3)`` and ``(2, 3)``.

**EDIT:** We can generalize this result, using only Gallina. We define
a boolean function ``is_prime`` that we prove correct w.r.t. the
inductive specification ``prime``. I guess this can be done in a more
elegant way, but I am confused with all the lemmas related to ``Z``.
Moreover, some of the definitions are opaque and cannot be used (at
least directly) to define a computable function.
|*)

Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.
Require Import Bool.
Require Import Recdef.

(** [for_all] checks that [f] is true for any integer between 1 and [n] *)
Function for_all (f : Z -> bool) n {measure Z.to_nat n} :=
  if n <=? 1 then true
  else f (n - 1) && for_all f (n - 1).
Proof.
  intros. apply Z.leb_nle in teq. apply Z2Nat.inj_lt; lia.
Defined.

Lemma for_all_spec : forall f n,
    for_all f n = true -> forall k, 1 <= k < n -> f k = true.
Proof.
  intros. assert (0 <= n) by lia. revert n H1 k H0 H.
  apply (natlike_ind
           (fun n => forall k : Z,
                1 <= k < n -> for_all f n = true -> f k = true)); intros.
  - lia.
  - rewrite for_all_equation in H2.
    destruct (Z.leb_spec0 (Z.succ x) 1).
    + lia.
    + replace (Z.succ x - 1) with x in H2 by lia. apply andb_true_iff in H2.
      assert (k < x \/ k = x) by lia. destruct H3.
      * apply H0; [lia | apply H2].
      * subst k. apply H2.
Qed.

Definition is_prime (p : Z) :=
  (1 <? p) && for_all (fun k => Z.gcd k p =? 1) p.

Theorem is_prime_correct : forall z, is_prime z = true -> prime z.
Proof.
  intros. unfold is_prime in H. apply andb_true_iff in H.
  destruct H as (H & H0). constructor.
  - apply Z.ltb_lt. assumption.
  - intros. apply for_all_spec with (k := n) in H0; try assumption.
    unfold rel_prime. apply Z.eqb_eq in H0. rewrite <- H0.
    apply Zgcd_is_gcd.
Qed.

(*| The proof becomes nearly as simple as @Arthur's one. |*)

Theorem prime113 : prime 113.
Proof.
  apply is_prime_correct; reflexivity.
Qed.

(*|
Answer (larsr)
**************

Fun fact: @epoiner's answer can be used together with Ltac in a proof
script for any prime number.

.. coq:: none
|*)

Reset Initial.
Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.

(*||*)

Theorem prime113 : prime 113.
Proof.
  constructor.
  - lia.
  - intros n H;
      repeat match goal with
             | H : 1 <= ?n < ?a  |- _ =>
               assert (Hn: n = a - 1 \/ 1 <= n < a - 1) by lia;
                 clear H; destruct Hn as [Hn | H];
                   [subst n; apply Zgcd_is_gcd | simpl in H; try lia]
             end.
Qed.

(*|
However, the proof term gets unwieldy, and checking becomes slower and
slower. This is why it small scale reflection (ssreflect) where
computation is moved into the type checking probably is preferrable in
the long run. It's hard to beat @Arthur Azevedo De Amorim's proof:
``Proof. reflexivity. Qed.`` :-) Both in terms of computation time,
and memory-wise.
|*)
