(*|
##########################################
How can I generalise Coq proofs of an iff?
##########################################

:Link: https://stackoverflow.com/questions/65588333/how-can-i-generalise-coq-proofs-of-an-iff
|*)

(*|
Question
********

A common kind of proof I have to make is something like
|*)

Context (T : Type) (Q : T -> T -> T -> Prop) (P : T -> T -> Prop).
Lemma my_lemma : forall y,
    (forall x x', Q x x' y) -> (forall x x', P x y <-> P x' y).
Proof.
  intros y Q_y.
  split.
  - admit. (* some proof using Q *)
  - admit. (* the same proof using Q, but x and x' are swapped *)
Abort. (* .none *)

(*|
where ``Q`` is itself some kind of iff-shaped predicate.

My problem is that the proofs of ``P x y -> P x' y`` and ``P x' y -> P
x y`` are often basically identical, with the only difference between
that the roles of ``x`` and ``x'`` are swapped between them. Can I ask
Coq to transform the goal into

.. code-block:: coq

    forall x x', P x y -> P x' y

which then generalises to the iff case, so that I don't need to repeat
myself in the proof?

I had a look through the standard library, the tactic index, and some
SO questions, but nothing told me how to do this.
|*)

(*|
Answer
******

In mathematics, one often can make "assumptions" "*without loss of
generality*" (WLOG) to simplify proofs of this kind. In your example,
you could say "assume *without loss of generality* that ``P x y``
holds. To prove ``P x y <-> P x' y`` it is sufficient to prove ``P x'
y``."

If you are using ``ssreflect``, you have the `wlog tactic
<https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#variants-the-suff-and-wlog-tactics>`__.

You essentially ``cut`` in another goal which can easily solve your
goal. You can also do it with standard tactics like ``assert`` or
``enough`` (which is like ``assert`` but the proof obligations are in
the other order).

An example to show what I mean: below I just want to show the
implication in one direction, because it can easily solve the
implication in the other direction (with ``firstorder``).
|*)

Goal forall x y, P x y <-> P y x.
  enough (forall x y, P x y -> P y x) by firstorder.

(*|
Now I just have to show the goal in one direction, because it implies
the real goal's both directions.

For more about WLOG see for instance `1
<https://www.cl.cam.ac.uk/~jrh13/papers/wlog.pdf>`__
|*)
