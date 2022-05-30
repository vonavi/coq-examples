(*|
##################################################################
How to return a (``intro``'d) hypothesis back to the goal formula?
##################################################################

:Link: https://stackoverflow.com/q/32567436
|*)

(*|
Question
********

For the proof:
|*)

Parameters A B : Prop.
Goal A -> B.
  intro H.

(*| I get: |*)

  Show. (* .unfold .messages *)

(*|
How do I return then ``A`` back to the goal section? To return to:
|*)

  revert H. (* .none *) Show. (* .unfold .messages *) Undo. (* .none *)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

Use the ``revert`` tactic:
|*)

  revert H.

(*|
It is exactly the inverse of ``intro``, cf. `the reference manual
<https://coq.inria.fr/distrib/current/refman/Reference-Manual010.html#hevea_tactic39>`__.
|*)

(*|
Answer (Konstantin Weitz)
*************************

You can use the ``revert`` tactic.

Given Coq's plethora of tactics, each with various corner cases and
varying quality of documentation, it's quite common that you won't
know which tactic to use.

In such cases, I find it useful to think of your proof as a program
(see Curry-Howard Isomorphism) and to ask yourself what term you would
have to write to solve your goal. The advantages of this approach is
that Coq's term language is easier to learn (because there just aren't
that many different kinds of terms) and expressive enough to solve all
goals solvable with tactics (sometimes the proofs are more verbose
though).

You can use the `refine
<https://coq.inria.fr/refman/Reference-Manual010.html#hevea_tactic7>`__
tactic to write your proofs in the term language. The argument of
``refine`` is a term with holes ``_``. ``refine`` discharges the
current goal using the term and generates a subgoal for every hole in
the term. Once you know how ``refine`` works, all you have to do is to
come up with a term that does what you want. For example:

- revert a hypothesis ``h`` with ``refine (_ h)``.
- introduce a hypothesis ``h`` with ``refine (fun h => _)``.
- duplicate a hypothesis ``h`` with ``refine ((fun h' => _) h)``.

Note that Coq's tactics tend to do quite a bit of magic behind the
scenes. For example, the ``revert`` tactic is "smarter" than the
``refine`` above when dealing with dependent variables:
|*)

Reset Initial. (* .none *)
Goal forall n : nat, n >= 0.
  intro n. revert n. (* .unfold *)
  Restart.
  intro n. refine (_ n). (* .unfold *)
  Restart.
  intro n'. refine ((_ : forall n, n >= 0) n'). (* .unfold *)
Abort.
