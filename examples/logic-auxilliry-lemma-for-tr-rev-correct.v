(*|
#############################################
Logic: auxilliry lemma for ``tr_rev_correct``
#############################################

:Link: https://stackoverflow.com/q/55991920
|*)

(*|
Question
********

In Logic chapter a tail recursive version of reverse list function is
introduced. We need to prove that it works correctly:
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

(* Tail recursion rev *)
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(*| But before proving it I wanted to prove a lemma: |*)

Lemma rev_append_app: forall (X : Type) (x : X) (l : list X),
    rev_append l [x] = rev_append l [] ++ [x].
Proof.
  intros X x l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. (* .unfold *)
Abort. (* .none *)

(*| Here I am stuck. What to do next? |*)

(*|
Answer (Simon)
**************

As you noticed during your attempted proof, when taking the induction
step from ``rev_append l [x]`` to ``rev_append (h :: t) [x]``, you end
up with the term ``rev_append t [h; x]`` after simplification. The
induction step does not lead towards the base case of the
``rev_append`` function, but to another recursive invocation that you
cannot simplify.

Notice how the induction hypothesis that you would like to apply makes
a statement about ``rev_append t [x]`` for some fixed ``x``, but in
your goal, the extra ``h`` list element before it gets in the way, and
the induction hypothesis is of no use.

This is what Bubbler's answer was referring to when stating that your
induction hypothesis is not strong enough: it only makes a statement
about the case where the second argument is a list with a *single
element*. But even after just the induction step (one recursive
application), that list already has at least two elements!

As suggested by Bubbler, the helper lemma ``rev_append l (l1 ++ l2) =
rev_append l l1 ++ l2`` is stronger and does not have this problem:
when used as the induction hypothesis, it can be applied to
``rev_append t [h; x]`` as well, allowing you to prove equality with
``rev_append t [h] ++ [x]``.

When attempting to prove the helper lemma, you may get stuck (like I
did) in the same way as when proving ``rev_append_app`` itself. The
crucial bit of advice that helped me proceed was to **be careful which
of the universally quantified variables you introduce before you start
the induction**. If you specialize any of them too early on, you might
weaken your induction hypothesis and become stuck again. You may need
to change the order of these quantified variables or use the
``generalize dependent`` tactic (see the `Tactics
<https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html>`__
chapter of *Logic Foundations*\ ).
|*)

(*|
Answer (Bubbler)
****************

You can see that the induction hypothesis ``IH`` is not strong enough
to prove the goal. Here what you need is **a more general statement to
prove in the first place**. You can find more exercises dedicated to
this topic `here
<https://homes.cs.washington.edu/~jrw12/InductionExercises.html>`__.
(Actually, tail-recursive reverse is one of the exercises.)

In your case, the fully generalized statement could be as follows:
|*)

Lemma rev_append_app': forall (X : Type) (l l1 l2 : list X),
        rev_append l (l1 ++ l2) = rev_append l l1 ++ l2.
Admitted. (* .none *)

(*|
Proving this by induction is trivial. Then you can prove your own
statement as a corollary of this one:
|*)

Corollary rev_append_app: forall (X : Type) (x : X) (l : list X),
    rev_append l [x] = rev_append l [] ++ [x].
Proof. intros. apply (rev_append_app' _ _ [] [x]). Qed.

(*|
Answer (xingfe123)
******************

use the generalize dependent tactic like this:
|*)

Reset rev_append_app. (* .none *)
Lemma rev_append_app: forall (X : Type) (l l1 : list X) (x : X),
    rev_append l (l1 ++ [x]) = rev_append l l1 ++ [x].
  intros. generalize dependent l1. induction l as [| h t IH].
  - intros. easy.
  - intros. apply (IH (h :: l1)).
Qed.
