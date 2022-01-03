(*|
################################
Proof leaking in Coq extraction?
################################

:Link: https://stackoverflow.com/q/51844640
|*)

(*|
Question
********

In order to understand how general recursive ``Function`` definitions
works, and how they comply with Coq's structural recursion constraint,
I tried to reimplement it on the Peano natural numbers. I want to
define recursive ``nat -> nat`` functions that can use any previous
values, not just the predecessor. Here is what I did:
|*)

Require Import Coq.Arith.PeanoNat. (* .none *)
Definition nat_strong_induction_set
           (* erased at extraction, type specification *)
           (P : nat -> Set)
           (* The strong induction step. To build the P n it can, but
              does not have to, recursively query the construction of
              any previous P k's. *)
           (ind_step : forall n : nat, (forall k : nat, (lt k n -> P k)) -> P n)
           (n : nat) :
  P n.
Proof.
  (* Force the hypothesis of ind_step as a standard induction
     hypothesis *)
  assert (forall m k : nat, lt k m -> P k) as partial_build.
  { induction m.
    - intros k H. now apply Nat.nlt_0_r in H.
    - intros k H. apply ind_step. intros k0 H0.
      apply IHm. apply Nat.lt_le_trans with k.
      + assumption.
      + apply Nat.lt_succ_r. assumption. }
  { apply (partial_build (S n) n). apply Nat.lt_succ_diag_r. }
Defined.

(*|
I used some custom lemmas on nats that I didn't paste here. It works,
I managed to define the euclidean division ``div a b`` with it, which
recursively uses ``div (a-b) b``. The extraction is almost what I
expected:
|*)

Require Extraction. (* .none *)
Extraction nat_strong_induction_set. (* .unfold .messages *)

(*|
Except for the ``n0`` parameter. We see that the only effect of this
parameter is to stop the recursion at the ``S n``-nth step. The
extraction also mentions that this ``assert false`` should not happen.
So why is it extracted? This seems better

.. code-block:: ocaml

    let nat_strong_induction_set ind_step n =
      let rec f k = ind_step k (fun k0 _ -> f k0)
      in f n

It looks like a glitch of Coq's structural recursion constraint, to
ensure the termination of all recursions. The Coq definition of
``nat_strong_induction_set`` writes ``lt k n``, so Coq knows only
previous ``P k``'s will be queried. This makes a decreasing chain in
the nats, which is forced to terminate in less than ``S n`` steps.
This allows a structural recursive definition on an additional fuel
parameter ``n0`` starting at ``S n``, it won't affect the result. So
if it is only a part of the termination proof, why is it not erased by
the extraction?
|*)

(*|
Answer
******

Your match is not erased because your definition mixes two things: the
termination argument, where the match is needed, and the
computationally relevant recursive call, where it isn't.

To force erasure, you need to convince Coq that the match is
computationally irrelevant. You can do so by making the termination
argument -- that is, the induction on ``m`` -- produce the proof of a
proposition instead of a function of type ``forall m k, lt k m -> P
k``. Luckily, the standard library provides an easy way of doing so,
with the ``Fix`` combined:
|*)

Require Import Coq.Arith.Wf_nat.

Reset nat_strong_induction_set. (* .none *)
Definition nat_strong_induction_set
           (P : nat -> Set)
           (ind_step : forall n : nat, (forall k : nat, (lt k n -> P k)) -> P n)
           (n : nat) :
  P n :=
  Fix Nat.lt_wf_0 P ind_step n.

(*|
Here, ``Nat.lt_wf_0`` is a proof that ``lt`` is well-founded. When you
extract this function, you get
|*)

Extraction nat_strong_induction_set. (* .unfold .messages *)

(*|
which is exactly what you wanted.

(As an aside, note that you don't need well-founded recursion to
define division -- check for instance how it is defined in the
`Mathematical Components library
<http://ssr.msr-inria.inria.fr/doc/mathcomp-1.5/MathComp.div.html>`__.)
|*)
