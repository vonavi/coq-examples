(*|
#######################################
Using ``Omega`` to prove a lemma in Coq
#######################################

:Link: https://stackoverflow.com/q/13690147
|*)

(*|
Question
********

I am trying to make a proof in Coq using ``Omega``. I spent a lot of
time on it, but nothing came to me. I have to say I am new in Coq, so
I am not at ease with this kind of language, and I do not have much
experience. But I am working on it.

Here's the code I have to prove:
|*)

Require Import Arith.

Fixpoint div2 (n : nat) :=
  match n with
  | S (S p) => S (div2 p)
  | _ => 0
  end.

Fixpoint mod2 (n : nat) :=
  match n with
  | S (S p) => mod2 p
  | x => x
  end.

(*|
To make this proof, I thought it would help to prove by induction this
lemma first:
|*)

Lemma div2_eq : forall n, 2 * div2 n + mod2 n = n.
Abort. (* .none *)

(*| Then this one, using ``omega`` and ``div2_eq``: |*)

Lemma div2_le : forall n, div2 n <= n.
Abort. (* .none *)

(*|
But I did not manage to go further.

Does anyone know what to do?
|*)

(*|
Answer
******

You can easily derive induction principles from the functions ``div2``
and ``mod2`` like so:
|*)

Require Import FunInd.

Functional Scheme div2_ind := Induction for div2 Sort Prop.
Functional Scheme mod2_ind := Induction for mod2 Sort Prop.

(*| ``div2_ind`` and ``mod2_ind`` have more or less types: |*)

Check div2_ind. (* .unfold .messages *)
Check mod2_ind. (* .unfold .messages *)

(*|
To apply these theorems you can conveniently write ``functional
induction (div2 n)`` or ``functional induction (mod2 n)`` where you
might usually write ``induction n``.

But a stronger induction principle is associated with these functions:
|*)

Lemma nat_ind_alt : forall P1 : nat -> Prop,
    P1 0 ->
    P1 1 ->
    (forall n1, P1 n1 -> P1 (S (S n1))) ->
    forall n1, P1 n1.
Proof.
  intros P1 H1 H2 H3. induction n1 as [[| [| n1]] H4] using lt_wf_ind.
  - info_auto.
  - info_auto.
  - info_auto.
Qed.

(*|
In fact, the domain of any function is a clue to a useful induction
principle. For example, the induction principle associated to the
domain of the functions ``plus : nat -> nat -> nat`` and ``mult : nat
-> nat -> nat`` is just structural induction. Which makes me wonder
why ``Functional Scheme`` doesn't just generate these more general
principles instead.

In any case, the proofs of your theorems then become:
|*)

Require Import Lia.

Lemma div2_eq : forall n, 2 * div2 n + mod2 n = n.
Proof.
  induction n as [| | n1 H1] using nat_ind_alt.
  - simpl in *. lia.
  - simpl in *. lia.
  - simpl in *. lia.
Qed.

Lemma div2_le : forall n, div2 n <= n.
Proof.
  induction n as [| | n1 H1] using nat_ind_alt.
  - simpl. lia.
  - simpl. lia.
  - simpl. lia.
Qed.

(*|
You should familiarize yourself with functional induction, but more
importantly, you should really familiarize yourself with well-founded
induction.
|*)
