(*|
########################################
How to destruct pair equivalence in Coq?
########################################

:Link: https://stackoverflow.com/q/30297109
|*)

(*|
Question
********

I'm trying to destruct a pair equivalence hypothesis in proof when
using Coq. But I didn't find the tactic for me.

The case is:

.. coq:: none
|*)

Section Foo.

  Variables a b a' b' : nat.
  Hypothesis H0 : (a, b) = (a', b').

  Goal False.

(*||*)

    Show. (* .unfold .hyps *)

(*| I want to destruct the pairs in H0 to generate |*)

    injection H0. (* .none *) clear H0. (* .none *)
    intros. (* .unfold .hyps *)

(*|
How can I achieve this? Which tactic should I use? Or should I define
lemma for destructing such pair?
|*)

(*|
Answer (Atsby)
**************

Use ``injection H0`` followed by ``intros`` as a first approximation.
|*)

(*|
Answer (Martin Huschenbett)
***************************

You can also do it in one step with ``inversion H0``.

----

**Q:** I still have a question: ``inversion H0`` also rewrites ``a``
to ``a'`` in my current goal. If I just want to split the hypothesis,
how can I do that?
|*)
