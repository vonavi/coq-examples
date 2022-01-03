(*|
#####################################
Structural recursion on two arguments
#####################################

:Link: https://stackoverflow.com/q/55704472
|*)

(*|
Question
********

I have tried to make a function in Coq which has a pretty complex
termination argument. To make it easier, I am able to write the
function so that it has a natural number as first argument, so that
either the number or the argument after it is structurally smaller.

When trying the nested fix approach to recursion on two arguments, Coq
complains that a proof argument that contains the semantics of the
decreasing number is not an inductive type.

I could probably do well-founded recursion manually, but I would like
to use Program Fixpoint or Equations. With Program Fixpoint I get a
very ugly version of the well-foundedness proof. Below is a minimal
code example that demonstrates the ugliness.
|*)

Require Import Program.

Inductive tuple_lt : (nat * nat) -> (nat * nat) -> Prop :=
  fst_lt : forall a b c d, a < c -> tuple_lt (a, b) (c, d).

Program Fixpoint f (a : nat) (b : nat) {measure (a, b) tuple_lt} :=
  match a with
  | 0 => 0
  | S n => f n b
  end.

Next Obligation.
  apply fst_lt. auto.
Qed.

Next Obligation.
  unfold well_founded. unfold MR.

(*| The obligation looks like this: |*)

  Show 1. (* .unfold .messages *)
Abort. (* .none *)

(*|
Can I somehow transform a proof of ``Acc tuple_lt`` into that ugly
proof or avoid generating it?

Is there a proof in the standard library for structural recursion on
two arguments?

How do I even write a manual WF proof using Equations? The manual does
not mention that.
|*)

(*|
Answer
******

In simple cases like this one, you shouldn't have to unfold
definitions such as ``well_founded`` and ``MR``, but rather use
appropriate lemmas.

To deal with ``MR``, you can use lemma ``measure_wf`` in Program.Wf.

To prove the well-foundedness of ``tuple_lt``, you can rely on lemmas
showing the well-foundedness of a relation based on the
well-foundedness of another relation. Here, we can use
``well_founded_lt_compat``. In other cases, you may find other lemmas
useful, such as ``wf_inverse_image``, ``well_founded_ltof`` or
``well_founded_gtof``.

The proof of the well-foundedness of ``tuple_lt`` becomes simple.
|*)

Require Import Coq.Arith.Wf_nat. (* .none *)
Lemma tuple_lt_wf : well_founded tuple_lt.
Proof.
  apply well_founded_lt_compat with fst.
  intros ? ? []; assumption.
Defined.

(*| And so does the proof of the second obligation. |*)

Next Obligation.
  apply measure_wf. apply tuple_lt_wf.
Defined.

(*|
(Note that in both cases, you should end the proofs with ``Defined``
instead of ``Qed``, if you want your function defined by ``Program
Fixpoint`` to compute inside Coq (otherwise it gets stuck on opaque
proofs); it seems that you can end the proof of the first obligation
with ``Qed``, though).

You could also use the following simpler definition for ``tuple_lt``:
|*)

Reset tuple_lt. (* .none *)
Require Import Coq.Arith.Wf_nat. (* .none *)
Definition tuple_lt (p1 p2 : nat * nat) := fst p1 < fst p2.

(*| In that case, the proof of well-foundedness is trivial. |*)

Lemma tuple_lt_wf : well_founded tuple_lt.
Proof.
  apply well_founded_ltof.
Defined.
