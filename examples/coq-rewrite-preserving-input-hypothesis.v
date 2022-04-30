(*|
############################################
Coq: ``rewrite`` preserving input hypothesis
############################################

:Link: https://stackoverflow.com/q/45175257
|*)

(*|
Question
********

I would like to rewrite a hypothesis while keeping the old version,
and saving the result of the rewrite under a new name. How should I do
that?
|*)

(*|
Answer
******

This is the shorter I can think of:
|*)

Lemma test T (P : T -> Prop) (x y : T) (heq : x = y) (hp : P x) : False.
Proof.
  pose proof hp. rewrite heq in hp.

(*|
However YMMV, usually when using ssreflect I get to manage my
hypotheses in such a way that I don't have to resort to these tricks
often.
|*)
