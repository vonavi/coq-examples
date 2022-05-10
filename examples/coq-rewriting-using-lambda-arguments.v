(*|
####################################
Coq rewriting using lambda arguments
####################################

:Link: https://stackoverflow.com/q/43849824
|*)

(*|
Question
********

We have a function that inserts an element into a specific index of a
list.
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Fixpoint inject_into {A} (x : A) (l : list A) (n : nat) : option (list A) :=
  match n, l with
  | 0, _        => Some (x :: l)
  | S k, []     => None
  | S k, h :: t => let kwa := inject_into x t k
                   in match kwa with
                      | None => None
                      | Some l' => Some (h :: l')
                      end
  end.

(*|
The following property of the aforementioned function is of relevance
to the problem (proof omitted, straightforward induction on ``l`` with
``n`` not being fixed):
|*)

Theorem inject_correct_index : forall A x (l : list A) n,
    n <= length l -> exists l', inject_into x l n = Some l'.
Admitted. (* .none *)

(*|
And we have a computational definition of permutations, with ``iota
k`` being a list of nats ``[0...k]``:

.. coq:: none
|*)

Require Import Coq.Arith.Factorial.

Fixpoint iota k :=
  match k with
  | 0 => [k]
  | S k' => iota k' ++ [k]
  end.

(*||*)

Fixpoint permute {A} (l : list A) : list (list A) :=
  match l with
  | []     => [[]]
  | h :: t => flat_map (
                  fun x => map (
                               fun y => match inject_into h x y with
                                        | None => []
                                        | Some permutations => permutations
                                        end
                             ) (iota (length t))) (permute t)
  end.

(*| The theorem we're trying to prove: |*)

Theorem num_permutations : forall A (l : list A) k,
    length l = k -> length (permute l) = fact k.

(*|
By induction on ``l`` we can (eventually) get to following goal:

.. coq:: none
|*)

Proof.
  intros A l. induction l; intros k H.
  - now subst k.
  - destruct k as [| k]; inversion H. specialize (IHl k H1).
    unfold fact. fold fact.

(*||*)

    Show. (* .unfold .messages *)

(*|
If we now simply ``cbn``, the resulting goal is stated as follows:
|*)

    cbn. (* .none *) Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
Here I would like to proceed by ``destruct (inject_into a x y)``,
which is impossible considering ``x`` and ``y`` are lambda arguments.
Please note that we will never get the ``None`` branch as a result of
the lemma ``inject_correct_index``.

How does one proceed from this proof state? (Please do note that I am
not trying to simply complete the proof of the theorem, that's
completely irrelevant.)
|*)

(*|
Answer
******

There is a way to rewrite under binders: the ``setoid_rewrite`` tactic
(see `§27.3.1
<https://coq.inria.fr/refman/Reference-Manual030.html#sec787>`__ of
the Coq Reference manual).

However, **direct** rewriting under lambdas is not possible without
assuming an axiom as powerful as the axiom of functional
extensionality (`functional_extensionality
<https://coq.inria.fr/library/Coq.Logic.FunctionalExtensionality.html#functional_extensionality>`__).

Otherwise, we could have proved:
|*)

(* classical example *)
Goal (fun n => n + 0) = (fun n => n).
  Fail setoid_rewrite <- plus_n_O.
Abort.

(*|
See `here
<https://sympa.inria.fr/sympa/arc/coq-club/2005-02/msg00002.html>`__
for more detail.

Nevertheless, if you are willing to accept such axiom, then you can
use the approach described by Matthieu Sozeau in `this
<http://thread.gmane.org/gmane.science.mathematics.logic.coq.club/3587>`__
Coq Club post to rewrite under lambdas like so:
|*)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Generalizable All Variables.

Instance pointwise_eq_ext {A B : Type} `(sb : subrelation B RB eq)
  : subrelation (pointwise_relation A RB) eq.
Proof.
  intros f g Hfg. apply functional_extensionality.
  intro x; apply sb, (Hfg x).
Qed.

Goal (fun n => n + 0) = (fun n => n).
  setoid_rewrite <- plus_n_O.
  reflexivity.
Qed.
