(*|
can coq intros pattern split at the rightmost opportunity for conjunction?
==========================================================================

https://stackoverflow.com/questions/63381511/can-coq-intros-pattern-split-at-the-rightmost-opportunity-for-conjunction
|*)

(*|
Question
--------

I am wondering if there is some intro pattern which can introduce `A
/\ B /\ C` as
|*)

Goal forall A B C, A /\ B /\ C -> A /\ B. (* .none *)
  intros A B C [HA [HB H2]]. (* .none *)
  assert (A /\ B) as H1 by (split; [exact HA | exact HB]). (* .none *)
  clear HA HB. (* .none *) move H2 after H1. (* .unfold .hyps *)
  exact H1. (* .none *)
Qed. (* .none *)

(*| I'm aware that `intros [H1 H2]` will produce |*)

Goal forall A B C, A /\ B /\ C -> B /\ C. (* .none *)
  intros A B C [H1 H2]. (* .unfold .hyps *)
  exact H2. (* .none *)
Qed. (* .none *)

(*|
but cannot figure out how to configure the brackets for the other
direction. This is a trivial example; but I have a more complicated
combination of conjunctions and disjunctions that I would much prefer
to destruct from right to left.

Thanks,
|*)

(*|
Answer
------

The `_ /\ _` notation in Coq is a right-associative *binary* operator,
so `A /\ B /\ C` really stands for `A /\ (B /\ C)`. If you want to
build some `A /\ B` you should first fully decompose the `/\ `
(`intros [HA [HB HC]].`, you can nest the patterns arbitrarily) and
then build the `A /\ B` hypothesis (for instance using `assert (A /\
B) as HAB by (split; [exact HA| exact HB]).` or any other way you
prefer to add an hypothesis).

In a more complex setting, you might want to write a lemma `and_assoc
: forall A B C, A /\ B /\ C -> (A /\ B) /\ C` and use a
*view*-pattern. Starting from a goal `A /\ B /\ C -> P` you can use
`intros [HAB HC]%and_assoc.` to obtain `HAB : A /\ B` and `HC : C` :
the `pat%and_assoc` part says that `and_assoc` should be applied first
to the top assumption and then further destructed with `pat`.
|*)
