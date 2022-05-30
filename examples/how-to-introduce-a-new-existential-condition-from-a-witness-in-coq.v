(*|
###################################################################
How to introduce a new existential condition from a witness in Coq?
###################################################################

:Link: https://stackoverflow.com/q/33140390
|*)

(*|
Question
********

My question relates to how to construct an ``exist`` term in the set
of conditions/hypotheses.

I have the following intermediate proof state:

.. coq:: none
|*)

Require Import Coq.Logic.ClassicalFacts.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle, not. intros exm X P H x.
  specialize (exm (P x)). destruct exm; auto.

(*||*)

  Show. (* .unfold .messages *)

(*|
In my mind, I know that because of ``H0``, ``x`` is a witness for
``(exists x : X, P x -> False)``, and I want to introduce a name:

.. code-block:: coq

    w : (exists x : X, P x -> False)

based on the above reasoning and then use it with ``apply H in w`` to
generate a ``False`` in the hypothesis, and finally ``inversion`` the
``False``.

But I don't know what tactic/syntax to use to introduce the witness
``w`` above. The best I can reach so far is that
|*)

  Check (H (ex_intro (fun x => P x -> False) x H0)).

(*|
gives ``False``.

Can someone explain how to introduce the existential condition, or an
alternative way to finish the proof?

P.S. What I have for the whole theorem to prove is:
|*)

Reset Initial. (* .none *)
Require Import Coq.Logic.ClassicalFacts. (* .none *)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle, not.
  intros exm X P H x.
  destruct (exm (P x)).
  - apply H0.
  - Check (H (ex_intro (fun x => P x -> False)  x H0)).

(*|
----

**A:** Note that it is not necessary to ``unfold`` ``excluded_middle``
or ``not`` to use them.
|*)

(*|
Answer (eponier)
****************

Here, since you already know how to construct a term of type
``False``, you can add it to the context using ``pose proof``. This
gives:
|*)

    pose proof (H (ex_intro (fun x => P x -> False)  x H0)).

(*|
You can even directly destruct the term, which solves the goal.
|*)
    Undo. (* .none *)
    destruct (H (ex_intro (fun x => P x -> False)  x H0)).

(*|
Another way to finish your proof is to prove ``False``. You can change
the goal to ``False`` with tactics like ``exfalso`` or
``contradiction``. With this approach, you can use hypotheses of the
form ``_ -> False`` that are otherwise difficult to manipulate. For
your proof, you can write:
|*)
    Undo. (* .none *)
    exfalso. apply H. (* or directly, contradiction H *)
    exists x. assumption.

(*|
----

**Q:** Thanks. It's interesting because I tried
|*)

    Undo 4. (* .none *)
    induction (H (ex_intro (fun x => P x -> False)  x H0)).

(*|
but it didn't work. Could you explain why ``destruct`` worked here
instead?

**A:** Actually, it works for me. Maybe it is due to the underscore
you are using. ``ex_intro`` expects 4 parameters, but the first one is
implicit, so it is not needed to specify it. I will edit my answer.
But I do not understand why it passes type-checking for you.

**Q:** My fault, I tried ``inversion`` (not ``induction``) trying to
``inversion`` the ``False``. But it didn't work. Do you know why
``destruct``/``induction`` works while ``inversion`` doesn't?

**A:**
It also works for me. After
|*)
    Undo. (* .none *)
    pose proof (H (ex_intro (fun x => P x -> False) x H0)).
    inversion H1.

(*|
solves the goal. What did you try to inverse? Note that you must
invert the hypothesis of type ``False``, not ``False`` itself.
|*)

(*|
Answer (Vinz)
*************

You could use the assert tactic:
|*)

    Undo. (* .none *) assert (w: exists x, P x -> False).

(*|
It will ask you to prove this statement in a new sub-goal, and will
add ``w`` to your existing goal. For this kind of trivial proof, you
can inline the proof directly:
|*)
    Undo. (* .none *)
    assert (w: exists x, P x -> False) by (exists x; exact H0).
