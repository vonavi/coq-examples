(*|
####################################
Removing trivial match clause in Coq
####################################

:Link: https://stackoverflow.com/q/66179133
|*)

(*|
Question
********

Consider the following example:
|*)

Definition cast {A : Set} (B : Set) (prf : A = B) (x : A)   : B.
  rewrite prf in x.
  refine x.
Defined.

Lemma castLemma0 {A : Set} : forall (x : A) prf, cast A prf x = x.
Proof.
  intros. compute. (* ??? *)

(*|
After the compute step, we are left with the following context and
subgoal
|*)

  Show 1. (* .unfold .messages *)

(*|
Clearly the left hand side and right hand side are equal. But I am not
sure how to get rid of the annoying ``match`` clause on the left hand
side. In particular, trying to ``destruct prf`` yields the following
error
|*)

  Fail destruct prf. (* .unfold .fails .messages *)

(*| Is there a way to get rid of this match clause? |*)

(*|
Answer
******

This is not provable in Coq without assuming an extra axiom, usually
``eq_rect_eq`` or something equivalent (Uniqueness of Identity Proofs
(UIP) or Axiom K).

If you restrict ``castLemma0`` to the ``eq_refl`` case, that is
``forall (x : A), cast A eq_refl x = x``, this is provable by
reflexivity.

One way to understand why this is not provable, is to accept that it
is consistant to assume an axiom ``bool_eq_not : bool = bool`` such
that ``cast bool bool_eq_not x = not x``. Plugging in ``bool_eq_not``
for ``prf`` in ``castLemma0`` would imply that ``not x = x``, which is
certainly wrong.

Proving that this is possible requires demonstrating a model of type
theory where ``bool_eq_nat`` is constructible. This was first done in
the paper "The groupoid interpretation of type theory", by Martin
Hofmann and Thomas Streicher. There have since been several other
models, including a model in simplicial sets by Voevodsky, and several
constructive models in cubical sets. These investigations are one
aspect of the field of Homotopy Type Theory (HoTT).

----

As a side note, there is a somewhat recently added (and still
experimental) feature `SProp (documentation)
<https://coq.inria.fr/refman/addendum/sprop.html>`__ that if you also
``Set Definitional UIP`` lets you prove this.
|*)
