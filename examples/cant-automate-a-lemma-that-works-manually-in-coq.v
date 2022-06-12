(*|
#################################################
Can't automate a lemma that works manually in Coq
#################################################

:Link: https://stackoverflow.com/q/30156837
|*)

(*|
Question
********

(It seems that `my previous question
<https://stackoverflow.com/questions/29978765/why-does-hint-resolve-x-fail-where-lets-x-works>`__
had too much irrelevant information, so I tried to abstract away the
details. I'm not sure it's still the same problem, but I'll delete the
other question if the same solution works for both.)

I'm trying to reason about some custom-defined lists and predicates:
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Inductive alphabet := A.

Definition sentence : Type := list alphabet.

Variable pred1 : sentence -> Prop.

Variable pred2 : sentence -> Prop.

Variable conclusion : Prop.

(*| Now, with the following hypotheses, |*)

Hypothesis H1 : forall (X : sentence),
    pred1 X -> pred2 (X ++ X).

Hypothesis H2 : forall X,
    pred2 X -> conclusion.

(*| I want to prove |*)

Example manual : pred1 [A] -> conclusion.

(*|
Which is obviously true, since ``conclusion`` follows whenever some
``sentence`` has ``pred2``, and ``pred1`` for any ``sentence`` implies
that the repetition of that ``sentence`` has ``pred2``. A hand-written
proof would be
|*)

intro. eapply H2. apply H1. exact H. Qed.

(*|
Notice that the proof uses nothing but ``intro``, ``apply``,
``eapply``, and ``exact``. This means that the proof should allow a
straightforward automation, as long as ``H1`` and ``H2`` are available
in the context. For instance, a semi-automatic version
|*)

Example semiauto : pred1 [A] -> conclusion.
pose proof H1. pose proof H2. eauto. Qed.

(*|
works exactly as you would expect. Now, let's try a fully automated
version with hints:
|*)

Hint Resolve H1 H2.

Example auto : pred1 [A] -> conclusion.
eauto.
intro. eauto.
eapply H2. eauto.
apply H1. eauto.
Qed.

(*|
This is strange. ``eauto`` fails not only in the beginning, but for
every step except the last. Why does this happen?

Some guesses : the consequent of ``H1`` includes the form ``X ++ X``,
which might be causing problems with unification. Perhaps Coq performs
some implicit cleanup with ``H1`` when it is explicitly introduced to
context, but not when it's just in hint DB.

Any ideas?

----

**A:** I don't have an answer, but ``eauto using H1, H2.`` solves your
goal. I don't know why it doesn't pick up the hints from the hint
database...

**A:** Putting ``debug`` infront of ``eauto``, i.e. ``debug eauto
using H1, H2.`` shows the search that takes place. And when in proof
mode, ``Print Hint.`` prints which hints are applicable at each
moment. For some reason, ``H1`` and ``H2`` are applicable, but
``eauto`` doesn't try them.
|*)

(*|
Answer (Jason Gross)
********************

The issue is transparency of ``sentence``.

Building on Anton Trunov's answer, if you look very closely, you'll
notice that a difference between ``Print HintDb core`` and ``Create
HintDb foo``. ``Print HintDb foo.`` is that ``Print HintDb core`` says

::

    Unfoldable variable definitions: none.
    Unfoldable constant definitions: none

while ``Create HintDb foo.`` ``Print HintDb foo.`` says

::

    Unfoldable variable definitions: all
    Unfoldable constant definitions: all

I constructed the following simplified version of your example:
|*)

Reset Initial. (* .none *)
Require Import Coq.Lists.List.
Import ListNotations.

Definition sentence := list nat.
Variable pred1 : sentence -> Prop.
Variable pred2 : sentence -> Prop.
Hypothesis H1 : forall (X : sentence),
    pred1 X -> pred2 (X ++ X).

Create HintDb foo.
Hint Resolve H1 : foo.
Hint Resolve H1 : bar.
Hint Resolve H1.

Example ex1 : pred1 [0] -> exists X, pred2 X.
  eexists.
  debug eauto.
Abort. (* .none *)

(*|
Here, we have that ``eauto`` and ``eauto with bar`` (and ``eauto with
bar nocore``, which removes the core database from ``eauto``'s
consideration) both fail, but ``eauto with foo`` (and ``eauto with foo
nocore``) succeeds. This suggests that the issue is transparency. A
bit of playing around resulted in me discovering that ``eauto`` will
work if we write
|*)

Hint Transparent sentence.

(*|
Additionally, even without this, ``eauto`` works fine if we explicitly
give the ``X`` variable the unfolded type:
|*)

Example ex2 : pred1 [0] -> exists X : list nat, pred2 X.

(*|
I am not entirely sure why Coq behaves this way... perhaps it is
refusing to unify evars with terms which are of different types (if
``?X`` has type ``sentence`` when ``X ++ X`` has type ``list``), or
perhaps it is a holdover of meta-based unification... I've opened an
`issue on the bugtracker about this lack of documentation / bad
behavior <https://github.com/coq/coq/issues/6862>`__.
|*)

(*|
Answer (Anton Trunov)
*********************

A possible workaround here is to add the hints to a new user-defined
database:

.. coq:: none
|*)

Reset Initial.

Require Import List.
Import ListNotations.

Inductive alphabet := A.
Definition sentence : Type := list alphabet.

Variable pred1 : sentence -> Prop.
Variable pred2 : sentence -> Prop.
Variable conclusion : Prop.

Hypothesis H1 : forall (X : sentence),
    pred1 X -> pred2 (X ++ X).
Hypothesis H2 : forall X,
    pred2 X -> conclusion.

(*||*)

Create HintDb my_hints.
Hint Resolve H1 H2 : my_hints.

(*| Now we can finish the proof: |*)

Example auto : pred1 [A] -> conclusion.
eauto with my_hints. Qed.

(*|
One more thing: Coq's reference manual tells (`§8.9.1
<https://coq.inria.fr/refman/Reference-Manual010.html#sec402>`__) us
that

    One can optionally declare a hint database using the command
    ``Create HintDb``. If a hint is added to an unknown database, it
    will be automatically created.

But if we omit the ``Create HintDb my_hints.`` part, the ``eauto``
tactic won't work. It looks like the same thing is going on when the
hints are being added to the default ``core`` hint database.
|*)
