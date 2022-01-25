(*|
#######################################################
How does decidable equality works with ``List.remove``?
#######################################################

:Link: https://stackoverflow.com/q/46589021
|*)

(*|
Question
********

I am starting in Coq and discovered that I have to provide a proof of
decidable equality to use ``List.remove``, e.g.
|*)

Require Import Coq.Lists.List.
Import List.ListNotations.

Inductive T : Set := A | B | C.

Lemma eq_dec : forall a b : T, {a = b} + {a <> b}.
Proof.
  destruct a, b; try (left; reflexivity); try (right; congruence).
Qed.

Definition f (xs : list T) : list T := List.remove eq_dec A xs.

(*| This now type-checks, but I don't understand how to use it. |*)

Theorem foo : f [A; B; C] = [B; C].
Proof. Fail reflexivity. (* .unfold .fails *)
Abort. (* .none *)

(*|
How does this decidable equality work and what is some good source I
could read about it?

Edit 1
======

I just learned about the `decide equality
<https://coq.inria.fr/distrib/8.6.1/refman/Reference-Manual010.html#hevea_tactic174>`__
tactic, which

    solves a goal of the form ``forall x y : R, {x=y} + {~x=y}``,
    where ``R`` is an inductive type such that its constructors do not
    take proofs or functions as arguments, nor objects in dependent
    types.

So ``eq_dec`` can rewriten:
|*)

Reset eq_dec. (* .none *)
Lemma eq_dec : forall a b : T, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(*|
Edit 2
======

I just learned about the `Scheme Equality for T
<https://coq.inria.fr/distrib/8.6.1/refman/Reference-Manual015.html#hevea_command235>`__
command, which

    Tries to generate a Boolean equality and a proof of the
    decidability of the usual equality. If identi involves some other
    inductive types, their equality has to be defined first.

So ``T_beq : T -> T -> bool`` and ``T_eq_dec : forall x y : T, {x = y}
+ {x <> y}`` can be automatically generated.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

The problem is that you used the ``Qed`` command to end your proof.
This causes the ``eq_dec`` function you just defined to become opaque,
thus preventing Coq from simplifying expressions involving it. A
simple solution in this case is to use ``Defined`` instead:
|*)

Reset Initial. (* .none *)
Require Import Coq.Lists.List.
Import List.ListNotations.

Inductive T : Set := A | B | C.

Lemma eq_dec : forall a b : T, {a = b} + {a <> b}.
Proof.
  destruct a, b; try (left; reflexivity); try (right; congruence).
Defined.

Definition f (xs : list T) : list T := List.remove eq_dec A xs.

Theorem foo : f [A; B; C] = [B; C].
Proof. reflexivity. Qed.

(*|
You can check Adam Chlipala's `CPDT book
<http://adam.chlipala.net/cpdt/html/Subset.html>`__ to learn more
about this style of programming.

There is also an alternative approach, which I personally prefer. The
idea is to program normal equality tests that return booleans, and
prove after the fact that the tests are correct. This is useful for
two reasons.

1. It allows reusing standard boolean operators to write these
   functions; and
2. functions that involve proofs (like ``eq_dec``) can interact badly
   with Coq's reduction machinery, because the reduction needs to take
   the proofs into account.

You can read more about this alternative style in the `Software
Foundations book
<https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html#lab223>`__.
You can also have a look at the `mathematical components
<https://math-comp.github.io/math-comp/>`__ library, which uses this
style pervasively -- for example, to define a notion of `type with
decidable equality
<http://ssr.msr-inria.inria.fr/~jenkins/current/mathcomp.ssreflect.eqtype.html>`__.
|*)

(*|
Answer (Yves)
*************

You can also keep the proof of decidable equality opaque, but in this
case you have to use another tactic than ``reflexivity`` to prove your
result.

In the same context as your example, try this:
|*)

Reset foo. (* .none *)
Theorem foo : f [A; B; C] = [B; C].
Proof.
  unfold f. simpl.
  case (eq_dec A A); [intros _ | intros abs; case abs; auto].
  case (eq_dec A B); [discriminate | intros _].
  case (eq_dec A C); [discriminate | intros _].
  reflexivity.
Qed.

(*|
Knowing that this solution exists may be very useful when you want to
reason more abstractly about the equality between elements of your
type and when computation cannot do everything for you.

----

**Q:** Could this pattern be automated using Ltac? i.e. a
``reduce_eq_dec x y`` that would detect whether ``x`` is syntactically
equal to ``y`` and use either the ``case`` or ``discriminate``
approach you highlighted?

**A:** yes, and using ``try`` you don't even have to be able to tested
whether ``x`` and ``y`` really are equal.
|*)
