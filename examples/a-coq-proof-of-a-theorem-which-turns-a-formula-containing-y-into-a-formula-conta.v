(*|
##################################################################################################
A Coq proof of a theorem which turns a formula containing ``y`` into a formula containing ``f(x)``
##################################################################################################

:Link: https://stackoverflow.com/questions/50231559/a-coq-proof-of-a-theorem-which-turns-a-formula-containing-y-into-a-formula-conta
|*)

(*|
Question
********

I am trying to prove:
|*)

Goal forall (T : Type) (U : Type) (P : T -> U -> Prop),
    (forall (x : T), exists (y : U), P x y)
    -> (exists (f : T -> U), forall (x : T), P x (f x)).
Abort. (* .none *)

(*|
In plain English, what I am trying to do is express the ability to
turn ``y`` into ``f(x)`` in a formula. For example, changing ``y = x +
1`` to ``f(x) = x + 1``.

A proof of the goal with the implication arrow reversed (turning
``f(x)`` into ``y``) takes 4 lines. However, with this goal I can't
think of anything to do after ``intros``.

I'm not even sure this is possible in Coq. If not, is there a better
way to express what I'm trying to do?
|*)

(*|
Answer
******

Your result is a form of the axiom of choice and cannot be proved in
Coq without extra axioms. The problem is that in order to construct
``f`` you need to extract the element ``y : U`` from the proof of
``exists y, P x y``. This is forbidden in Coq by design, to ensure
that proofs have no computational significance.

A way to get around this restriction is to replace the usual
existential by its computationally relevant counterpart. We then get
what Bob Harper calls *the theorem of choice*:
|*)

Goal forall (T : Type) (U : Type) (P : T -> U -> Prop),
    (forall (x : T), { y : U | P x y })
    -> (exists (f : T -> U), forall (x : T), P x (f x)).
Proof.
  intros T U P H. exists (fun x => proj1_sig (H x)).
  intros x. now apply proj2_sig.
Qed.
