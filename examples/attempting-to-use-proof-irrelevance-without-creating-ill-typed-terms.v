(*|
####################################################################
Attempting to use proof irrelevance without creating ill-typed terms
####################################################################

:Link: https://stackoverflow.com/q/47853843
|*)

(*|
Question
********

To illustrate the issue I am facing let us assume we have a predicate
on ``nat``:
|*)

Parameter pred : nat -> Prop.

(*|
Let us assume further that we have a type which encapsulates data, as
well as a proof that the encapsulated data satisfies a certain
property. For example:
|*)

Inductive obj : Type :=
| c : forall (n : nat), pred n -> obj.

(*|
Now we would like to regard two objects ``c n p`` and ``c m q`` to be
the same objects as long as ``n = m``, regardless of the proofs
involved to build them. So let us introduce a proof irrelevance axiom:
|*)

Axiom irrel : forall (P : Prop) (p q : P), p = q.

(*|
Now given this axiom, it is expected that the equality ``c n p = c m
q`` be provable for ``n = m``:
|*)

Theorem obvious : forall (n m : nat) (p : pred n) (q : pred m),
    n = m -> c n p = c m q.
Abort. (* .none *)

(*|
Now I have been playing around with this for a while, and none of the
typical ``rewrite`` tactics can work as they create ill-typed terms. I
am guessing the theorem should be true within Coq's type theory (given
the proof irrelevance axiom) but probably involves some trick unknown
to a beginner. Any suggestion is greatly appreciated.
|*)

(*|
Answer
******

TL;DR
=====
|*)

Theorem obvious n m (p : pred n) (q : pred m) :
  n = m -> c n p = c m q.
Proof.
  intros ->. rewrite (irrel _ p q). reflexivity.
Qed.

(*|
Explanation
===========

Let me show how one can use information containing in error messages
to come up with a solution:
|*)

Reset obvious. (* .none *)
Theorem obvious n m (p : pred n) (q : pred m) :
  n = m -> c n p = c m q.
Proof.
  intros E. Fail rewrite E. (* .fails *)

(*| At this point we get the following error message: |*)

  Fail rewrite E. (* .unfold .messages *)

(*|
The ``rewrite`` tactic tried to build the proof term using
``eq_ind_r`` lemma. Let us look at its type:
|*)

  Check eq_ind_r. (* .unfold .messages *)

(*|
``rewrite`` tries to build the following term:

.. code-block:: coq

    @eq_ind_r _ m (fun x => c x p = c m q) (subgoal : c m p = c m q) n E.

which is ill-typed:
|*)

  Fail Check @eq_ind_r _ m (fun x => c x p = c m q).
  (* .fails .unfold .messages .in *)

(*|
This means that the link between ``n`` and ``pred n`` has been lost at
this point and we can restore it by saying explicitly that ``x`` and
``p`` must comply with each other by generalizing over ``p``:
|*)

  Check @eq_ind_r _ m (fun x => forall (p : pred x), c x p = c m q).

(*|
The above means we can proceed to finish the proof in the following
manner:
|*)

  revert p. rewrite E. intro p.
  rewrite (irrel _ p q). reflexivity.
Qed.

(*|
The original version of the code uses intro-pattern ``intros ->`` to
achieve the effect of the longer ``intros E; revert p; rewrite E;
intros p.`` for this particular case.
|*)
