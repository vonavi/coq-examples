(*|
##################################################################
What does it mean when Coq expands a function as part of the goal?
##################################################################

:Link: https://stackoverflow.com/q/54336455
|*)

(*|
Question
********

I was trying to solve the following theorem and got stuck at the last
``simpl.``:

.. coq:: none
|*)

Require Import List.
Import ListNotations.

Definition natlist := list nat.

Fixpoint nonzeros (l : natlist) :=
  match l with
  | [] => []
  | 0 :: xs => nonzeros xs
  | x :: xs => x :: nonzeros xs
  end.

(*||*)

Lemma nonzeros_app : forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n' l' IHl'].
  - simpl. reflexivity.
  - simpl.

(*| at that point Coq changes the goal from: |*)

    Undo. (* .none *) Show 1. (* .unfold .messages *)

(*| to: |*)

    simpl. (* .none *) Show 1. (* .unfold .messages *)
Abort. (* .none *)

(*|
which seems completely mysterious to me. What does it mean when Coq
just copy pastes the definition of a function into my goal? What do I
even do with this?

----

Context of Question:
====================

Someone told me that the solution is:
|*)

Lemma nonzeros_app : forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n' l' IHl'].
  - simpl. reflexivity.
  - simpl. { induction n'.
             - (* ... *) admit. (* .none *)

             - (* ... *) admit. (* .none *) }
Abort. (* .none *)

(*|
which made me want to understand why they use induction on ``n'``
since it feels it would never occur to me to use induction there. So I
am asking, why? But I realized that before I could ask that why I
didn't even understand the proof state before that since it just
seemed to copy paste a function to a proof state (which makes no sense
to me). So before I asked why use induction there I have to ask what
does the proof state before that, maybe that would yield light into
why induction on ``n'``.
|*)

(*|
Answer
******

I am assuming that you have defined ``nonzeros`` in the following way
(or similar):
|*)

Reset Initial. (* .none *)
Require Import List.
Import ListNotations.

Definition natlist := list nat.

Fixpoint nonzeros (l : natlist) :=
  match l with
  | [] => []
  | 0 :: xs => nonzeros xs
  | x :: xs => x :: nonzeros xs
  end.

(*|
So that ``nonzeros`` is recursive with structural decreasing on ``l``.
Coq's ``simpl`` tactic employs a heuristic in which it unfolds
definitions of fixpoints if they are applied to a term that has a
constructor as the head symbol. In your case, e.g., ``nonzeros (n' ::
l')``, the constant ``nonzeros`` is followed by a term formed by a
constructor, ``Cons`` (=\ ``::``). Coq performs a so-called "delta
reduction", replacing the occurrence of ``nonzeros`` with its
definition. Since that definition is a ``match``, you get a ``match``
as your new term. Further substitutions do simplify it a bit, but
cannot eliminate the two cases: one for zero head and one for nonzero
head.

Same happens to the occurrence ``nonzeros ((n' :: l') ++ l2)``, which
is first simplified to ``nonzeros (n' :: (l' ++ l2))``, so that again,
the head of the argument is ``Cons``.

If you want to avoid exposing ``match`` expressions when simplifying,
you can put the following directive after the definition of
``nonzeros``:
|*)

Arguments nonzeros l : simpl nomatch.

(*|
This specifically tells ``simpl`` to avoid expanding a term if this
will end up exposing a ``match`` at the location of the change.

As for the ``induction`` used by your friend here: it is applied to
force a case split over ``n'``, so that each case (``n' = 0``, ``n' =
S _``) can be handled separately. Indeed, induction is not needed
here. A simple case split (``case n'``) will do the same.
|*)
