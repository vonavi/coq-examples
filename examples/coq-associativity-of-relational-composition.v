(*|
############################################
Cow: Associativity of relational composition
############################################

:Link: https://stackoverflow.com/q/70377028
|*)

(*|
Question
********

I am working on verifying a system based on relation algebra. I found
D. Pous's relation algebra library popular among the Coq society.

https://github.com/damien-pous/relation-algebra

On this page, binary relation ``hrel`` is defined together with its
relational composition ``hrel_dot``.

http://perso.ens-lyon.fr/damien.pous/ra/html/RelationAlgebra.rel.html

In this library, a binary relation is defined as
|*)

Universe U.
Definition hrel (n m : Type@{U}) := n -> m -> Prop.

(*|
And the relational composition of two binary relations is defined as
|*)

Definition hrel_dot n m p (x : hrel n m) (y : hrel m p) : hrel n p :=
  fun i j => exists2 k, x i k & y k j.

(*| I believe that the relational composition is associative, i.e. |*)

Lemma dot_assoc :
  forall m n p q (x : hrel m n) (y : hrel n p) (z : hrel p q),
    hrel_dot m p q (hrel_dot m n p x y) z = hrel_dot m n q x (hrel_dot n p q y z).

(*|
I got to the place where I think the LHS and RHS of the expressions
are equivalent, but I have no clues about the next steps.
|*)

  intros. (* .none *) unfold hrel_dot. (* .none *)
  Show. (* .unfold .messages *)

(*|
I don't know how to reason about the nested ``exists2``, although the
results seem straightforward by exchanging the variables ``k`` and
``k0``.

----

**A (Ana Borges):** I'm not sure you can prove the *equality* of those
two expressions, at least not without proof irrelevance. If you
rewrite your goal as a logical equivalence things should be easier.
|*)

(*|
Answer
******

As Ana pointed out, it is not possible to prove this equality without
assuming extra axioms. One possibility is to use functional and
propositional extensionality:
|*)

Reset Initial. (* .none *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Universe U.
Definition hrel (n m : Type@{U}) := n -> m -> Prop.

Definition hrel_dot n m p (x : hrel n m) (y : hrel m p) : hrel n p :=
  fun i j => exists2 k, x i k & y k j.

Lemma dot_assoc :
  forall m n p q (x : hrel m n) (y : hrel n p) (z : hrel p q),
    hrel_dot m p q (hrel_dot m n p x y) z = hrel_dot m n q x (hrel_dot n p q y z).
Proof.
  intros m n p q x y z.
  apply functional_extensionality. intros a.
  apply functional_extensionality. intros b.
  apply propositional_extensionality.
  unfold hrel_dot; split.
  - intros [c [d ? ?] ?]. eauto.
  - intros [c ? [d ? ?]]. eauto.
Qed.
