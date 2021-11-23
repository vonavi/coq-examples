(*|
###################################################
Can any one help me how to prove this therom in coq
###################################################

:Link: https://stackoverflow.com/questions/69540976/can-any-one-help-me-how-to-prove-this-therom-in-coq
|*)

(*|
Question
********

This is the first part of my code:
|*)

Parameter D: Set.
Parameter x: D.
Parameter y: D.
Parameter R: D->Prop.

Lemma b: ~(exists x:D, ~ R x)->(forall y:D, R y).
Abort. (* .none *)

(*|
I have worked on it for quite a long time, but it seems that I cannot
use the left part of the implication well.

Can anyone help me figure out how to write the rest of of the code?
|*)

(*|
Answer
******

Your question is a bit vague, as you don't specify what ``D`` and
``R`` are, and where you are stuck in your proof. Try providing a
minimal working example, with an explicit ``fail`` tactic for where
you're stuck in the proof.

In *classical logic* (the one you're use to in maths), as you have the
*excluded middle* rule, you can always do a case analysis on whether
something is true or false. In vanilla Coq, built for *intuitionistic
logic*, it's not the case. Your result is actually *not provable* if
the predicate ``R`` is not decidable (if it's not either true or false
on every input : ``forall (x:D), R x \/ ~R x``), if the type ``D`` is
not empty.

Try adding the decidability of ``R`` as an hypothesis and reprove it.
It should follow more or less this structure (the key being the case
analysis on whether ``(R y)`` is true or false):
|*)

Lemma yourGoal :
  (forall x, R x \/ ~ R x) -> (* Decidability of R *)
  ~ (exists x, ~ R x) -> forall y, R y.
Proof.
  intros Hdec Hex y. (* naming the hypothesis for convenience *)
  specialize (Hdec y).
  destruct Hdec as [H_Ry_is_true | H_Ry_is_false]. (* case analysis, creates two goals *)
  + (* (R y) is true, which is our goal. *)
    assumption.
  + (* (R y) is false, which contradicts Hex *)
    exfalso. (* transform your goal into False *)
    apply Hex.
    (* should be easy from here, using the [exists] tactic *)
    now exists y.
Qed.

(*|
PS: this exact result (and its link with excluded middle) is mentioned
in Software foundations, which is a great resource to learn Coq and
logic:
https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html#not_exists_dist
|*)
