(*|
###################################################################
``Eval compute`` is incomplete when own decidability is used in Coq
###################################################################

:Link: https://stackoverflow.com/q/28478445
|*)

(*|
Question
********

The ``Eval compute`` command does not always evaluate to a simple
expression. Consider the code:
|*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Import ListNotations.

Inductive I : Set := a : nat -> I | b : nat -> nat -> I.

Lemma I_eq_dec : forall x y : I, {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.

(*| And, if I execute the following command: |*)

Eval compute in (if In_dec eq_nat_dec 10 [3;4;5] then 1 else 2).

(*|
Coq tells me that the result is ``2``. However, when I execute the
following expression:
|*)

Eval compute in (if In_dec I_eq_dec (a 2) [(a 1); (a 2)] then 1 else 2).

(*|
I get a long expression where the In-predicate seems to be unfolded,
but no result is given.

What do I have to change to obtain the answer ``1`` in the last ``Eval
compute`` line?
|*)

(*|
Answer
******

In Coq there are two terminator commands for proof scripts: ``Qed``
and ``Defined``. The difference between them is that the former
creates *opaque* terms, which cannot be unfolded, even by ``Eval
compute``. The latter creates transparent terms, which can then be
unfolded as usual. Thus, you just have to put ``Defined`` in the place
of ``Qed.``:
|*)

Reset Initial. (* .none *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Import ListNotations.

Inductive I : Set := a : nat -> I | b : nat -> nat -> I.

Lemma I_eq_dec : forall x y : I, {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Defined.

Eval compute in (if In_dec I_eq_dec (a 2) [(a 1); (a 2)] then 1 else 2).

(*|
I personally find the sumbool type ``{A} + {B}`` not very nice for
expressing decidable propositions, precisely because proofs and
computation are too tangled together; in particular, proofs affect how
terms reduce. I find it better to follow the `Ssreflect
<http://ssr.msr-inria.inria.fr/>`__ style, separate proofs and
computation and relate them via a special predicate:
|*)

Require Import ssreflect. (* .none *)
Inductive reflect (P : Prop) : bool -> Set :=
| ReflectT of P : reflect P true
| ReflectF of ~ P : reflect P false.

(*|
this gives a convenient way for saying that a boolean computation
returns true iff some property is true. Ssreflect provides support for
conveniently switching between the computational boolean view and the
logical view.
|*)
