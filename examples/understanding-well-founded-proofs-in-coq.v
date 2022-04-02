(*|
##########################################
Understanding "well founded" proofs in Coq
##########################################

:Link: https://stackoverflow.com/q/50204730
|*)

(*|
Question
********

I'm writing a fixpoint that requires an integer to be incremented
"towards" zero at every iteration. This is too complicated for Coq to
recognize as a decreasing argument automatically and I'm trying prove
that my fixpoint will terminate.

I have been copying (what I believe is) an example of a
well-foundedness proof for a step function on Z from the standard
library. `(Here) <https://coq.inria.fr/library/Coq.ZArith.Zwf.html>`__
|*)

Require Import ZArith. (* .none *)
Require Import ZArith.Zwf.

Section wf_proof_wf_inc.
  Variable c : Z.
  Let Z_increment (z : Z) := (z + ((Z.sgn c) * (-1)))%Z.

  Lemma Zwf_wf_inc : well_founded (Zwf c).
  Proof.
    unfold well_founded. intros a.

(*| which creates the following context: |*)

    Show. (* .unfold .messages *)
  Admitted. (* .none *)
End wf_proof_wf_inc. (* .none *)

(*|
My question is what does this goal actually mean?

I thought that the goal I'd have to prove for this would at least
involve the step function that I want to show has the "well founded"
property, "Z_increment".

The most useful explanation I have looked at is `this
<https://github.com/coq/coq/wiki/Inductive-and-Co-Inductive-Types>`__
but I've never worked with the list type that it uses and it doesn't
explain what is meant by terms like "accessible".
|*)

(*|
Answer
******

Basically, you don't need to do a well founded proof, you just need to
prove that your function decreases the (natural number) ``abs z``.
More concretely, you can implement ``abs (z : Z) : nat := z_to_nat (z
* Z.sgn z)`` (with some appropriate conversion to nat) and then use
this as a measure with ``Function``, something like ``Function foo z
{measure abs z} := ...``.

The well founded business is for showing *relations* are well-founded:
the idea is that you can prove your function terminates by showing it
"decreases" some well-founded relation ``R`` (think of it as ``<``);
that is, the definition of ``f x`` makes recursive subcalls ``f y``
only when ``R y x``. For this to work ``R`` has to be *well-founded*,
which intuitively means it has no infinitely descending chains. CPDT's
`general recursion chapter
<http://adam.chlipala.net/cpdt/html/Cpdt.GeneralRec.html>`__ as a
really good explanation of how this really works.

How does this relate to what you're doing? The standard library proves
that, for all lower bounds ``c``, ``x < y`` is a well-founded relation
in ``Z`` if additionally its only applied to ``y >= c``. I don't think
this applies to you - instead you move towards zero, so you can just
decrease ``abs z`` with the usual ``<`` relation on ``nat``\ s. The
standard library already has a proof that this relation is well
founded, and that's what ``Function ... {measure ...}`` uses.
|*)
