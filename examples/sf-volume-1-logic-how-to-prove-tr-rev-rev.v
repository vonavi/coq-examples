(*|
####################################################
SF Volume 1: Logic: How to prove ``tr_rev <-> rev``?
####################################################

:Link: https://stackoverflow.com/q/69360955
|*)

(*|
Question
********

From Software Foundations Volume 1, chapter Logic we see a tail
recursive definition of list reversal. It goes like so:

.. coq:: none
|*)

Require Import Lists.List Logic.FunctionalExtensionality.
Import ListNotations.

(*||*)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(*|
We're, then, asked to prove the equivalence of ``tr_rev`` and ``rev``
which, well, is pretty obvious that they are the same. I'm having a
hard time completing the induction, though. Would appreciate if the
community would provide any hints as to how to approach this case.

Here's as far as I got:
|*)

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X. (* Introduce the type *)
  apply functional_extensionality. (* Apply extensionality axiom *)
  intros l. (* Introduce the list *)
  induction l as [| x l']. (* start induction on the list *)
  - reflexivity. (* base case for the empty list is trivial *)
  - (* inductive case seems simple too. We unfold the definition *)
    unfold tr_rev. simpl. (* simplify it *)
    unfold tr_rev in IHl'. (* unfold definition in the Hypothesis *)
    rewrite <- IHl'. (* .unfold *) (* rewrite based on the hypothesis *)
Abort. (* .none *)

(*|
Now, ``[] ++ [x]`` is obviously the same as ``[x]`` but ``simpl``
can't simplify it and I couldn't come up with a ``Lemma`` that would
help me here. I *did* prove ``app_nil_l`` (i.e. ``forall (X : Type) (x
: X) (l : list X), [] ++ [x] = [x]``) but when I try to rewrite with
``app_nil_l`` it'll rewrite both sides of the equation.

I could just define that to be an axiom, but I feel like that's
cheating :-p

Thanks
|*)

(*|
Answer
******

Proving things about definitions with accumulators has a specific
trick to it. The thing is, facts about ``tr_rev`` must necessarily be
facts about ``rev_append``, but ``rev_append`` is defined on two
lists, while ``tr_rev`` is defined on only one. The computation of
``rev_append`` depends on these two lists, and thus the induction
hypothesis needs to be general enough to include both of these lists.
However, if you fix the second input of ``rev_append`` to always be
the empty list (which you implicitly do by stating your result only
for ``tr_rev``), then the induction hypothesis will always be too
weak.

The way around this is to first prove a general result for
``rev_append`` by induction on ``l1`` (and generalizing on ``l2``),
and then specializing this result for the case of ``tr_rev``.
|*)
