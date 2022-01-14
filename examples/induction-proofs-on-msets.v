(*|
#########################
Induction proofs on MSets
#########################

:Link: https://stackoverflow.com/q/47572526
|*)

(*|
Question
********

I'm trying to use MSet library in a Coq development and I need a
``smap`` function, which is absent from the library, but can be
implemented using ``fold``, as usual.

In the following `gist
<https://gist.github.com/rodrigogribeiro/1bb47d5a07e91e27384175fdb2710e34>`__,
I've put a simplification of what I'm working on, full of axioms, just
to get straight to the point.

My problem is to prove a property of the following ``smap`` function:

.. coq:: none
|*)

Require Import MSets.MSetRBT MSets.MSetProperties.

Axiom Exp : Set.

Module ExpOT <: Orders.OrderedType.
  Definition t := Exp.
  Definition eq := @eq Exp.
  Definition eq_equiv : Equivalence eq.
  Admitted.
  Axiom lt : t -> t -> Prop.
  Definition lt_strorder : StrictOrder lt.
  Admitted.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Admitted.
  Axiom compare : t -> t -> comparison.
  Definition compare_spec : forall e e',
      CompareSpec (eq e e') (lt e e') (lt e' e) (compare e e').
  Admitted.
  Definition eq_dec : forall (e e' : Exp), {e = e'} + {e <> e'}.
  Admitted.
End ExpOT.

Module Import MSet := MSetRBT.Make ExpOT.
Module Import MSetDec := MSetDecide.WDecideOn ExpOT MSet.
Module Import MSetProps := MSetProperties.WPropertiesOn ExpOT MSet.

(*||*)

Definition smap (f : Exp -> Exp) s :=
  MSet.fold (fun a ac => MSet.add (f a) ac) MSet.empty s.

(*|
Which uses ``fold`` from Coq MSet library. The property that I want to
show is:
|*)

Lemma smap_lemma : forall s f e,
    In e (smap f s) -> exists e', In e' s /\ e = f e'.
Proof.
  induction s using set_induction; intros; try fsetdec.
Abort. (* .none *)

(*|
Which is intended to show that if an element ``e`` in the set ``smap f
s``, then exists another element ``e'`` in ``s``, s.t. ``e = f e'``.
My difficulty is to prove the inductive case, since the induction
hypothesis produced by ``set_induction`` does not seems useful at all.

Could someone provide me any clues on how should I proceed?

----

**A:** A note about sets don't include a ``smap`` operation is because
it only makes sense as such if the mapped function is injective and
order-preserving. For all other cases, you are talking about "the
image of a set under f", which has slightly different properties.
|*)

(*|
Answer
******

First, I think there is a problem in your definition of ``smap``. You
must swap ``MSet.empty`` and ``s``, otherwise you can prove:
|*)

Lemma smap_trivial : forall f s, smap f s = s.
Proof.
  intros. reflexivity.
Qed.

(*|
With the right definition, you can use the ``fold_rec`` lemma that is
adapted to this kind of goal.
|*)
