(*|
#################################################################
Coq execution difference between semicolon ``;`` and period ``.``
#################################################################

:Link: https://stackoverflow.com/q/36292552
|*)

(*|
Question
********

Given a valid Coq proof using the ``;`` tactical, is there a general
formula for converting it to a valid equivalent proof with ``.``
substituted for ``;``?

Many Coq proofs use the ``;`` or tactic sequencing tactical. As a
beginner, I want to watch the individual steps execute, so I want to
substitute ``.`` for ``;``, but to my surprise I find that this may
break proof.

Documentation on ``;`` is sparse, and I haven't found an explicit
discussion of ``.`` anywhere. I did see a `paper
<http://www.ii.uni.wroc.pl/~mabi/papers/PPDP13.pdf>`__ that says
informal meaning of ``t1; t2`` is

    apply ``t2`` to every subgoal produced by the execution of ``t1``
    in the current proof context,

and I wonder if ``.`` only operates on the current subgoal and that
explains the different behavior? But especially I want to know if
there is a general solution to repairing the breakage caused by
substituting ``.`` for ``;``.
|*)

(*|
Answer
******

The semantics of ``tac1; tac2`` is to run ``tac1`` the and then run
``tac2`` on *all* the subgoals created by ``tac1``. So you may face a
variety of cases:

There are no goals left after running ``tac1``
==============================================

If there are no goals left after running ``tac1`` then ``tac2`` is
never run and Coq simply silently succeeds. For instance, in this
first derivation we have a useless ``; intros`` at the end of the
(valid) proof:
|*)

Goal forall A : Prop, A -> (A /\ A /\ A /\ A /\ A).
  intros; repeat split; assumption; intros.
Qed.

(*|
If we isolate it, then we get an ``Error: No such goal.`` because we
are trying to run a tactics when there is nothing to prove!
|*)

Goal forall A : Prop, A -> (A /\ A /\ A /\ A /\ A).
  intros; repeat split; assumption.
  Fail intros. (* .fails .unfold *)
Abort. (* .none *)

(*|
There is exactly one goal left after running ``tac1``
=====================================================

If there is precisely one goal left after running ``tac1`` then
``tac1; tac2`` behaves a bit like ``tac1. tac2``. The main difference
is that if ``tac2`` fails then so does the whole of ``tac1; tac2``
because the sequence of two tactics is seen as a unit that can either
succeed as a whole or fail as a whole. But if ``tac2`` succeeds, then
it's pretty much equivalent.

E.g. the following proof is a valid one:
|*)

Goal forall A : Prop, A -> (A /\ A /\ A /\ A /\ A).
  intros.
  repeat split; assumption.
Qed.

(*|
Running ``tac1`` generates more than one goal
=============================================

Finally, if multiple goals are generated by running ``tac1`` then
``tac2`` is applied to all of the generated subgoals. In our running
example, we can observe that if we cut off the sequence of tactics
after ``repeat split`` then we have 5 goals on our hands. Which means
that we need to copy / paste ``assumption`` five times to replicate
the proof given earlier using ``;``:
|*)

Goal forall A : Prop, A -> (A /\ A /\ A /\ A /\ A).
  intros; repeat split.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

(*|
----

**A:** I'll point out that probably the most *important* difference,
aside from applying the tactic in every branch, is that Coq will
backtrack through ``;``. E.g. even if ``tac1`` only ever generates one
goal, if there are multiple ways for it to do so (an important example
would be ``constructor``), then ``tac1. tac2`` will commit to the
first success and run ``tac2`` on it. ``tac1; tac2`` will make
``tac1`` try one thing, then try ``tac2`` after that, and if that
fails try ``tac1`` another way, and then try ``tac2`` after that, and
if that fails try ``tac1`` another *another* way, etc.
|*)