(*|
###############################################################################
Form of ``intros`` in Coq specifically for ``forall`` and explicitly for ``->``
###############################################################################

:Link: https://proofassistants.stackexchange.com/q/862
|*)

(*|
Question
********

Are there tactics in Coq that are more limited versions (subtactics?)
of ``intros``?

I'm curious if there are any specifically for ``forall ...`` and
specifically for ``->``.

----

``intros`` in Coq is capable of undoing the outermost ``forall`` as
well as the outermost ``->``.

It introduces hypotheses with provided or arbitrary names.

I suspect the reason for this generality is the fact that Coq is built
on top of the calculus of inductive constructions and ``forall`` and
``->`` really are both special cases of the dependent Π-type. (Also,
now that I think about it, ``forall`` might actually be the general
construction. I'm not sure.)

Here is an example from the ``Basics.v`` file from Software
Foundations. This is a theorem and proof provided by authors, not a
completed exercise from SF. (I mention this because the authors ask
people not to post solutions to SF problems online.)
|*)

Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.
Qed.

(*|
Anyway, the generality of ``intros`` is nice in theory, but it can
make tactic scripts harder to read. Are there weaker tactics than
``intros`` that can only unpack ``->`` or only unpack ``forall``? That
would make it easier to tell at a glance what roughly what "part" of a
theorem is being addressed by a tactic appearing in the middle of a
tactic script.
|*)

(*|
Answer
******

``intros *`` only unpacks ``forall``. `Example from the reference
manual
<https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#intropattern-star-ex>`__:
|*)

Goal forall A B : Prop, A -> B. (* .none *)
  Show. (* .unfold .messages *)
  intros *.
  Show. (* .unfold .messages *)
