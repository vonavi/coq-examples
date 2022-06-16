(*|
##################################
About the ``refine`` tactic in Coq
##################################

:Link: https://stackoverflow.com/q/28484450
|*)

(*|
Question
********

Consider the following lines (in Coq):
|*)

Variable A : Type.
Variables f g : A -> A.
Axiom Hfg : forall x, f x = g x.
Variable a b : A.
Axiom t : g a = g b.
Goal f a = g b.

(*| The tactic |*)

  refine (eq_trans (Hfg _) t).

(*|
solves the goal. That is, Coq is able to replace the hole by ``a``
without help. But the tactic
|*)

  Restart. (* .none *) refine (eq_trans (Hfg a) _).

(*| replaces the above goal by the goal |*)

  Show. (* .unfold .messages *)

(*|
But, Coq is unable to find ``t`` alone. Idem for the tactic ``refine
(eq_trans (Hfg _) _)``.

Is there a particular reason for Coq to be able to guess the first
hole and not the second hole?
|*)

(*|
Answer (Vinz)
*************

(I'm not 100% sure of what I'm writing here, but) Coq never 'guess'
anything, but it can infer information from more complex ones. Your
general scheme here is that you ask Coq to use transitivity of
equality to solve your goal. Therefore, Coq needs two statements of
equality to succeed.

In the first case, you give Coq everything it needs to solve the goal,
namely ``t : g a = g b`` and ``Hfg _ : f _ = g _``. Since ``eq_trans``
forces the ``_`` to be ``a``, there is nothing left to prove.

In the second case, you only feed coq ``Hfg a : f a = g a`` so it
misses ``g a = g b`` to solve the goal. Yes it is in the context, but
Coq will not use automation unless you ask it explicitly.

----

**Q:** And how is it possible to use automation in this case?

**A:** In your particular case, you would have to add your axiom ``t``
to a hint data base, in order to do something like ``refine (eq_trans
(Hfg _) _); auto with your_database_name`` (I'm not familiar with hint
databases, you should look at the manual). In more common cases where
the missing statement is in the context, you can happen
``;intuition``, ``;auto``, or ``;assumption`` to your refine, and it
will use the current context to try to solve the remaining goals.

**A:** From what I remember:
|*)

  Restart. (* .none *)
  Hint Resolve t. refine (eq_trans (Hfg _) _); auto.
Qed. (* .none *)

(*| should be enough here. |*)

(*|
Answer (Gilles 'SO- stop being evil')
*************************************

Your goal requires the two axioms ``Hfg`` and ``t``. Coq will only
ever use an axiom in a proof if it's given explicitly or if it finds
the axiom in a hint database. So your proof needs to make both ``Hfg``
and ``t`` appear.

``refine (eq_trans (Hfg _) t)`` contains both axioms. The argument to
``Hfg`` is imposed by the type of the term:

- ``eq_trans`` has a type of the form ``?1 = ?2 -> ?2 = ?3 -> ?1 =
  ?3``, and unifying the type of ``t`` with ``?2 = ?3`` yields ``?2 :=
  g a`` and ``?3 := g b``.
- ``Hfg _`` has a type of the form ``f ?4 = g ?4``, and unifying that
  with ``?1 = ?2`` yields ``?4 := a`` and thence ``?1 := f a``.

Coq is able to make this type inference, so the term is fully typed
and completes the proof.

In contrast, with ``refine (eq_trans (Hfg a) _)``, Coq applies what
it's given, and sees that there is a hole left in the proof: it
requires a proof of ``g a = g b``. This is an axiom, but Coq won't
apply it automatically: it leaves you the choice of deciding whether
to use this proof or, perhaps, some other proof of that fact.

A natural way to prove this goal would be to use the `rewrite tactic
<http://coq.inria.fr/distrib/8.4/refman/Reference-Manual010.html#hevea_tactic109>`__.
|*)

Goal f a = g b.
  rewrite Hfg. rewrite t. reflexivity.
Qed.

(*|
You can let Coq find the right equalities to apply by declaring the
axioms with `Hint Rewrite
<http://coq.inria.fr/distrib/8.4/refman/Reference-Manual010.html#hevea_command235>`__
then applying `autorewrite
<http://coq.inria.fr/distrib/8.4/refman/Reference-Manual010.html#hevea_tactic145>`__.
Note that ``autorewrite`` applies equalities blindly, it is not
influenced by the goal.
|*)

Hint Rewrite Hfg t : my_equalities.
Goal f a = g b.
  autorewrite with my_equalities. reflexivity.
Qed.

(*|
Alternatively, you can apply the `congruence tactic
<http://coq.inria.fr/distrib/8.4/refman/Reference-Manual010.html#hevea_tactic153>`__,
which takes care of chaining multiple equalities. You'll need to get
the axioms into the hypotheses first.
|*)

Goal f a = g b.
  generalize Hfg t. intros. congruence.
Qed.
