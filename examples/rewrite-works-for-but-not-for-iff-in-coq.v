(*|
################################################################
``rewrite`` works for ``=`` but not for ``<->`` (``iff``) in Coq
################################################################

:Link: https://stackoverflow.com/q/34239906
|*)

(*|
Question
********

Adapting @Matt's example,
|*)

Require Export Coq.Setoids.Setoid.

Inductive R1 : Prop -> Prop -> Prop :=
| T1_refl : forall P, R1 P P.

Inductive R2 : Prop -> Prop -> Prop :=
| T2_refl : forall P, R2 P P.

Theorem Requal : R1 = R2.
Admitted.

Theorem Requiv : forall x y, R1 x y <-> R2 x y.
Admitted.

Theorem test0 : forall y, R2 y y -> exists x, R1 x x.
Proof.
  intros. rewrite <- Requal in H. (*works*) rewrite Requal. (*works as well*)
Abort.

Theorem test2 : forall y, R2 y y -> exists x, R1 x x.
Proof.
  intros. rewrite <- Requiv in H. (*works*) Fail rewrite Requiv. (* .fails *) (*fails*)

(*| What confuses me is why the last step has to fail. |*)

  Show. (* .unfold .messages *)

(*|
Is this failure related to functional extensionality?

The error message is particularly confusing:
|*)

  Fail rewrite Requiv. (* .unfold .messages *)
Abort. (* .none *)

(*|
There is exactly one subterm matching ``R1 _ _``, namely ``R1 x x``.

Also, per @larsr, the rewrite works if ``eexists`` is used
|*)

Theorem test1 : forall y, R2 y y -> exists x, R1 x x.
Proof.
  intros. eexists. rewrite Requiv. (*works as well*) apply H.
Qed.

(*| What did ``eexists`` add here? |*)

(*|
Answer
******

The ``rewrite`` cannot go under the existential quantifier. You'll
need to instantiate ``t'`` first before you can do the rewrite. Note
that ``econstructor`` may be a useful tactic in this case, which can
replace the existential quantifier with a unification variable.

EDIT in response to OP's comment
================================

This will still not work for equality. As an example, try:
|*)

Reset Initial. (* .none *)
Inductive R1 : Prop -> Prop -> Prop :=
| T1_refl : forall P, R1 P P.

Inductive R2 : Prop -> Prop -> Prop :=
| T2_refl : forall P, R2 P P.

Theorem Req : forall x y, R1 x y = R2 x y.
Admitted.

Theorem test : forall y, R2 y y -> exists x, R1 x x.
Proof.
  intros. Fail rewrite Req. (* .fails *) (*rewrite still fails*)

(*|
The issue is not actually about equality vs. ``iff``, the issue
relates to rewriting under a binding (in this case a lambda). `The
implementation <https://coq.inria.fr/library/Coq.Init.Logic.html>`__
of ``exists x : A, P`` is really just syntax for ``ex A (fun x => P
x)``, so the rewrite is failing not because of the ``iff``, but
because the ``rewrite`` tactic does not want to go under the binding
for ``x`` in ``(fun x => P x)``. It seems as though there might be a
way to do this with `setoid_rewrite
<https://coq.inria.fr/refman/Reference-Manual029.html#sec756>`__,
however, I don't have any experience with this.

----

**A:** ``Require Import Coq.Setoids.Setoid.`` and then
``setoid_rewrite Requiv.`` should work under the existential
quantifier.
|*)
