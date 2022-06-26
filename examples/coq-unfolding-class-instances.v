(*|
##############################
Coq: unfolding class instances
##############################

:Link: https://stackoverflow.com/q/24111816
|*)

(*|
Question
********

How do I unfold class instances in Coq? It seems to be possible only
when the instance doesn't include a proof, or something. Consider
this:
|*)

Class C1 (t : Type) := {v1 : t}.
Class C2 (t : Type) := {v2 : t; c2 : v2 = v2}.

Instance C1_nat : C1 nat := {v1 := 4}.

#[refine] Instance C2_nat : C2 nat := {v2 := 4}.
trivial.
Qed.

Theorem thm1 : v1 = 4.
  unfold v1. unfold C1_nat. trivial.
Qed.

Theorem thm2 : v2=4.
  unfold v2. Fail unfold C2_nat. (* .fails *)

(*|
``thm1`` is proved, but I can't prove ``thm2``; it complains at the
``unfold C2_nat`` step with
|*)

  Fail unfold C2_nat. (* .unfold .messages *)

(*|
What's going on? How do I get to ``C2_nat``'s definition of ``v2``?

----

**A:** I think this transparent-opaque feature exists to allow
speeding up reduction. You should make opaque the parts of your
programs that don't contribute to the output, that contribute only to
the type.
|*)

(*|
Answer
******

You ended the definition of ``C2_nat`` with ``Qed``. Definitions
ending with ``Qed`` are opaque and cannot be unfolded. Write the
following instead
|*)

Reset C2_nat. (* .none *)
#[refine] Instance C2_nat : C2 nat := {v2 := 4}.
trivial.
Defined.

(*| and your proof finishes without problems. |*)
