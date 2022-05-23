(*|
################################################
Local ``Inductive`` definitions and ``Theorems``
################################################

:Link: https://stackoverflow.com/q/36235244
|*)

(*|
Question
********

I'm using a couple of ``Inductive`` definitions as counter examples in
some proofs. I would however like to encapsulate these definitions by
enclosing them in a ``Section``. Regular ``Definitions`` can be hidden
using ``Let``, but is this also possible for ``Inductive``
definitions? And how about ``Theorem``\ s?

Let me give the actual thing I'm trying to achieve, as I may be going
about it totally the wrong way in the first place. I want to formalize
all the proofs and exercises of the excellent book "Logics of Time and
Computation" by Robert Goldblatt into Coq.

For starters we take classical logic as that is what the book does as
well.
|*)

Require Import Classical_Prop.
Require Import Classical_Pred_Type.

(*|
Next we define identifiers the same way it is done in Software
Foundations.
|*)

Inductive id : Type := Id : nat -> id.

(*| Definition of the syntax. |*)

Inductive modal : Type :=
| Bottom : modal
| V : id -> modal
| Imp : modal -> modal -> modal
| Box : modal -> modal.

Definition Not (f : modal) : modal := Imp f Bottom.

(*| Definition of the semantics using Kripke frames. |*)

(* Inspired by: www.cs.vu.nl/~tcs/mt/dewind.ps.gz *)
Record frame : Type :=
  { Worlds : Type
  ; WorldsExist : exists w : Worlds, True
  ; Rel : Worlds -> Worlds -> Prop }.

Record kripke : Type :=
  { Frame : frame
  ; Label : (Worlds Frame) -> id -> Prop }.

Fixpoint satisfies (M : kripke) (x : Worlds (Frame M)) (f : modal) : Prop :=
  match f with
  | Bottom => False
  | V v => Label M x v
  | Imp f1 f2 => satisfies M x f1 -> satisfies M x f2
  | Box f => forall y : Worlds (Frame M), Rel (Frame M) x y -> satisfies M y f
  end.

(*| The first lemma relates the modal ``Not`` to the one of Coq. |*)

Lemma satisfies_Not : forall M x f, satisfies M x (Not f) = ~ satisfies M x f.
Proof. auto. Qed.

(*| Next we lift the semantics to complete models. |*)

Definition M_satisfies (M : kripke) (f : modal) : Prop :=
  forall w : Worlds (Frame M), satisfies M w f.

(*| And we show what it means for the ``Not`` connective. |*)

Lemma M_satisfies_Not : forall M f, M_satisfies M (Not f) -> ~ M_satisfies M f.
Proof.
  unfold M_satisfies.
  intros M f Hn Hcontra.
  destruct (WorldsExist (Frame M)).
  specialize (Hn x). clear H.
  rewrite satisfies_Not in Hn.
  specialize (Hcontra x). auto.
Qed.

(*|
Here comes the thing. The reverse of the above lemma does not hold and
I want to show this by a counter example, exhibiting a model for which
it doesn't hold.
|*)

Inductive Wcounter : Set := x1 : Wcounter | x2 : Wcounter | x3 : Wcounter.

Lemma Wcounter_not_empty : exists w : Wcounter, True.
Proof. exists x1. constructor. Qed.

Inductive Rcounter (x : Wcounter) (y : Wcounter) : Prop :=
| E1 : x = x1 -> y = x2 -> Rcounter x y
| E2 : x = x2 -> y = x3 -> Rcounter x y.

Definition Lcounter : Wcounter -> id -> Prop :=
  fun x i => match x with
             | x1 => match i with | Id 0 => True | _ => False end
             | x2 => match i with | Id 1 => True | _ => False end
             | x3 => match i with | Id 0 => True | _ => False end
             end.

Definition Fcounter : frame := Build_frame Wcounter Wcounter_not_empty Rcounter.

Definition Kcounter : kripke := Build_kripke Fcounter Lcounter.

(*|
Next an ``Ltac`` that relieves me from typing verbose ``assert``\ s.
|*)

Ltac counter_example H Hc :=
  match type of H with
  | ?P -> ~ ?Q => assert (Hc: Q)
  | ?P -> (?Q -> False) => assert (Hc: Q)
  | ?P -> ?Q => assert (Hc: ~Q)
  end.

(*|
Finally I use this counter example to prove the following ``Lemma``.
|*)

Lemma M_not_satisfies_Not :
  ~ forall M f, ~ M_satisfies M f -> M_satisfies M (Not f).
Proof.
  apply ex_not_not_all. exists Kcounter.
  apply ex_not_not_all. exists (V (Id 0)).
  unfold M_satisfies. simpl.
  intro Hcontra. unfold not in Hcontra.
  counter_example Hcontra Hn2.
  - apply ex_not_not_all. exists x1. simpl. auto.
  - apply Hn2. apply Hcontra. apply ex_not_not_all; exists x2. simpl. auto.
Qed.

(*|
Preferably I would have used the ``remember`` tactic to define the
counter example inside the proof, but I don't think it can be used for
the ``Inductive`` definitions. All the definitions relating to the
counter example are exported as part of my theory, which I prefer not
to do. It is only used in the proof of ``M_not_satisfies_Not``.
Actually I would not even want to export this ``Lemma`` either as it
is not very useful. I only put it there to argue that
``M_satisfies_Not`` can not be an equivalence.
|*)

(*|
Answer
******

``Section`` doesn't hide definitions, use ``Module`` instead. For
example put the counter example in a module.

.. code-block:: coq

    Module CounterExample.
      Import Definitions.
      Inductive Wcounter : Set := x1 | x2 | x3.
      ...
      Lemma M_not_satisfies_Not : ...
    End CounterExample.

At this stage, only ``CounterExample`` is defined at the top level.

If you don't want that either, then you could just put the definitions
in one ``.v`` file and the counter example in another file that
imports the definitions. Actually, the way it works is that ``.v``
files are turned into individual modules.
|*)
