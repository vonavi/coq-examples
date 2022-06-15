(*|
####################################################################################
In the Coq tactics language, what is the difference between ``intro`` and ``intros``
####################################################################################

:Link: https://stackoverflow.com/q/50033343
|*)

(*|
Question
********

In the Coq tactics language, what is the difference between ``intro``
and ``intros``?
|*)

(*|
Answer
******

``intro`` and ``intros`` behave differently if no argument is supplied
======================================================================

According to the reference manual:

    If the goal is neither a product nor starting with a let
    definition, the tactic ``intro`` applies the tactic ``hnf`` until
    the tactic ``intro`` can be applied or the goal is not
    head-reducible.

On the other hand, ``intros``, as a variant of ``intro`` tactic,

    repeats ``intro`` until it meets the head-constant. It never
    reduces head-constants and it never fails.

Example:
|*)

Goal not False.
  (* does nothing *)
  intros.
  (* unfolds `not`, revealing `False -> False`;
     moves the premise to the context *)
  intro.
Abort.

(*|
Note: both ``intro`` and ``intros`` do the same thing if an argument
is supplied (``intro contra`` / ``intros contra``).

``intros`` is polyvariadic, ``intro`` can only take 0 or 1 arguments
====================================================================
|*)

Goal True -> True -> True.
  (* Fail `intro t1 t2.` *)
  intros t1 t2.  (* or `intros` if names do not matter *)
Abort.

(*|
``intro`` does not support intro-patterns
=========================================
|*)

Goal False -> False.
  (* Fail `intro [].` *)
  intros [].
Qed.

(*|
Some information about intro-patterns can be found in the `manual
<https://coq.inria.fr/distrib/V8.8.0/refman/proof-engine/tactics.html#coq:tacn.intros>`__
or in the `Software Foundations
<https://softwarefoundations.cis.upenn.edu/>`__ book. See also `this
example
<https://github.com/tchajed/coq-tricks/blob/master/IntroPatterns.v>`__
of not-so-trivial combination of several intro-patterns.

``intros`` does not support ``after`` / ``before`` / ``at top`` / ``at bottom`` switches
========================================================================================

Let's say we have a proof state like this
|*)

Goal True -> (True /\ True) -> (True /\ True /\ True)
     -> (True /\ True /\ True /\ True -> True). (* .none *)
  intros H1 H2 H3. (* .none *) Show. (* .unfold .messages *)

(*|
then e.g. ``intro H4 after H3`` will modify the proof state like so:
|*)

  intro H4 after H3. (* .none *) Show. (* .unfold .messages *)

(*| and ``intro H4 after H1`` will produce |*)

  Undo. (* .none *) intro H4 after H1. (* .none *) Show. (* .unfold .messages *)
