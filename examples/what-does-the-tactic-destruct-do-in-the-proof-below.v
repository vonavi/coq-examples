(*|
What does the tactic destruct do in the proof below?
====================================================

:Link: https://stackoverflow.com/questions/69433292/what-does-the-tactic-destruct-do-in-the-proof-below
|*)

(*|
Question
--------

I was reading the series Software Foundations by Benjamin Pierce. And
in the Chapter Logic in the first book I came across a problem. In the
proof of the theorem
|*)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> forall x, P x.

(*|
And the proof of theorem can be as follows:
|*)

Proof.
  unfold excluded_middle.
  intros exmid X P H x.
  destruct (exmid (P x)) as [H1 | H2].
  - apply H1.
  - destruct H.
    exists x. apply H2.
Qed.

(*|
What puzzled me is the ``destruct H`` in the second case. What does
the tactic ``destruct`` do here? It seems different from What I've
known about it before. (``H`` here is ``~ (exists x : X, ~ P x)``).
After using ``destruct H``, the subgoal is tranformed from ``P x``
into ``exists x : X, ~ P x``.
|*)

(*|
Answer
------

When you destruct a term of the form ``A -> B`` you get a goal for
``A`` and the goals for what ``destruct B`` would result in. ``not A``
is defined as ``A -> False`` so ``B`` is ``False`` in your case and
``destruct B`` results in no goals. So you end up with just ``A``.

Here is a long form proof of what is going on:
|*)

Reset not_exists_dist. (* .none *)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> forall x, P x.
Proof.
  unfold excluded_middle.
  intros exmid X P H x.
  destruct (exmid (P x)) as [H1 | H2].
  - apply H1.
  - assert (ex (fun x : X => not (P x))) as H3.
    exists x. apply H2.
    specialize (H H3).
    destruct H.
Qed.

(*|
You can also replace ``destruct H`` with ``exfalso; apply H``.
|*)
