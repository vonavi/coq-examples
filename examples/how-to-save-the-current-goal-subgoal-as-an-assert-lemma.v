(*|
###########################################################
How to save the current goal/subgoal as an ``assert`` lemma
###########################################################

:Link: https://stackoverflow.com/q/33059783
|*)

(*|
Question
********

During a proof, I come to a situation where the current goal/subgoal
turned out to be useful in a later stage of the same theorem.

Is there a tactic to "save" the current goal as a lemma as if the
current goal is ``assert``\ ed?

Of course, I can copy&paste to ``assert`` the goal explicitly, or
write a separate Lemma before the current theorem. But I am just
curious if shortcuts exist.
|*)

(*|
Answer
******

Leaving this answer for future reference.

I don't know since when it exists, but maybe the `abstract
<https://coq.inria.fr/refman/proof-engine/ltac.html#coq:tacn.abstract>`__
tactic could help. It allows you to name a part of the proof and
re-use it later, even if you are in a different sub-goal.
|*)
