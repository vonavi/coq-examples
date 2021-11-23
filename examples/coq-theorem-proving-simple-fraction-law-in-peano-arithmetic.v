(*|
############################################################
Coq theorem proving: Simple fraction law in peano arithmetic
############################################################

:Link: https://stackoverflow.com/questions/59120093/coq-theorem-proving-simple-fraction-law-in-peano-arithmetic
|*)

(*|
Question
********

I am learning coq and am trying to prove equalities in peano
arithmetic.

I got stuck on a simple fraction law.

We know that ``(n + m) / 2 = n / 2 + m / 2`` from primary school. In
peano arithmetic this does only hold if n and m are even (because then
division produces correct results).
|*)

Require Import Arith Even.

Compute (3 / 2) + (5 / 2). (*3*)
Compute (3 + 5) / 2. (*4*)

(*| So we define: |*)

Theorem fraction_addition: forall n m: nat ,
    even n -> even m ->  Nat.div2 n + Nat.div2 m = Nat.div2 (n + m).

(*|
From my understanding this is a correct and provable theorem. I tried
an inductive proof, e.g.
|*)

  intros n m en em. induction n.
  - reflexivity.
  - (* .unfold *)
Abort. (* .none *)

(*|
So I don't find a way to apply the induction hypothesis.

After long research of the standard library and documentation, i don't
find an answer.
|*)

(*|
Answer (Anton Trunov)
*********************

You need to strengthen your induction hypothesis in cases like this.
One way of doing this is by proving an induction principle like this
one:
|*)

From Coq Require Import Arith Even.
Lemma nat_ind2 (P : nat -> Prop) :
  P 0 -> P 1 -> (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  now intros P0 P1 IH n; enough (H : P n /\ P (S n)); [|induction n]; intuition.
Qed.

(*| ``nat_ind2`` can be used as follows: |*)

Theorem fraction_addition n m :
  even n -> even m -> Nat.div2 n + Nat.div2 m = Nat.div2 (n + m).
Proof.
  induction n using nat_ind2.
  (* here goes the rest of the proof *)
Admitted.

(*|
Answer (larsr)
**************

You can also prove your theorem without induction if you are ok with
using the standard library.

If you use ``Even m`` in your hypothesis (which says ``exists n, m =
2*m``) then you can use simple algebraic rewrites with lemmas from the
standard library.
|*)

Require Import PeanoNat.
Import Nat.

Goal forall n m, Even n -> Even m -> n / 2 + m / 2 = (n + m) / 2.
  inversion 1; inversion 1.
  subst.
  rewrite <- mul_add_distr_l.
  rewrite ?(mul_comm 2).
  rewrite ?(div_mul); auto.
Qed.

(*|
The question mark just means "rewrite as many (zero or more) times as
possible".

``inversion 1`` does inversion on the first inductive hypothesis in
the goal, in this case first ``Even n`` and then ``Even m``. It gives
us ``n = 2 * x`` and ``m = 2 * x0`` in the context, which we then
substitute.

Also note ``even_spec: forall n : nat, even n = true <-> Even n``, so
you can use ``even`` if you prefer that, just rewrite with
``even_spec`` first...
|*)
