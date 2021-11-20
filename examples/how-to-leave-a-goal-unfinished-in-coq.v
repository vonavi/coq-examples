(*|
How to leave a goal unfinished in Coq
=====================================

:Link: https://stackoverflow.com/questions/60018942/how-to-leave-a-goal-unfinished-in-coq
|*)

(*|
Question
--------

In Isabelle, you can leave a goal unfinished in two ways:

- sorry: will leave your proof and the fact can be used in later
  proofs.
- oops: will leave the proof but the fact cannot be used in later
  proofs.

Is there similar functionality in Coq that would allow me to leave a
goal unfinished to come back later to it? This is useful to sketch the
structure of the proof while not filling in all the details. Note that
the approach in `How to switch the current goal in Coq?
<https://stackoverflow.com/questions/34421064/how-to-switch-the-current-goal-in-coq>`_
modifies the proof structure. That's not what I'm looking for.
|*)

(*|
Answer
------

You have several ways to terminate a proof in Coq. You probably know
`Qed` which asserts the proof is completed. There is also `Defined`
for when you want the proof to have computational content.

The things you are looking for are:

- `Admitted` which admits the proof, so it can be used later;
- `Abort` which gives up on proving the lemma.

They can be used that way:
|*)

Lemma foo : forall n, n = 0.
Proof.
  intro n. destruct n.
  - reflexivity.
  -
Abort.

Lemma bar : forall A (n : A), n = n.
Admitted.

(*|
In both cases you can have a partial proof script before the
`Admitted`/`Abort` or none at all.

As @HTNW points out, you can also use the equivalent tactics `admit`
and `give_up` inside subgoals of the proof. Using those, the proof
however *has* to be concluded using either `Admitted` or `Abort`.
|*)

Lemma lem : forall A, A + A -> A.
Proof.
  intros A h. destruct h.
  - admit.
  - give_up.
Admitted.

(*|
The partial proof is in any case thrown away with this solution. If
for some reason you want to keep using a partial proof (for instance
if you want to compute with it), a common trick is to use an axiom to
close the goals that you want to leave for later.
|*)

Reset lem. (* .none *)
Axiom cheating : forall A, A.

Tactic Notation "cheat" := apply cheating.

Lemma lem : forall A, A + A -> A.
Proof.
  intros A h. destruct h.
  - cheat.
  - cheat.
Defined. (* This is now ok *)

(*|
You have to be careful using that trick though. You can check that a
lemma has been proven without axioms using `Print Assumptions lem`. If
it says "closed under context" you're good, otherwise it will lists
the axioms it depends on and if `cheating` appears you know it's not
entirely proven.
|*)
