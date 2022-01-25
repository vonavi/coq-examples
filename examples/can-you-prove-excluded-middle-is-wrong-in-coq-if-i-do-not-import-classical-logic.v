(*|
################################################################################
Can you prove Excluded Middle is wrong in Coq if I do not import classical logic
################################################################################

:Link: https://stackoverflow.com/q/50078451
|*)

(*|
Question
********

I know excluded middle is impossible in the logic of construction.
However, I am stuck when I try to show it in Coq.
|*)

Theorem em : forall P : Prop, ~P \/ P -> False.

(*| My approach is: |*)

Proof.
  intros P H. unfold not in H. intuition.

(*| The system says following: |*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
How should I proceed? Thanks

----

**A:** `This question
<https://stackoverflow.com/q/32812834/2747511>`__ is strongly related,
but I think it's nevertheless different from the current one.

**A:** If you had a metatheory, you could prove that no Coq program
proves the law of the excluded middle. This would be closest to what
you are trying to prove.
|*)

(*|
Answer (Anton Trunov)
*********************

One cannot refute the law of excluded middle (LEM) in Coq. Let's
suppose you proved your refutation of LEM. We model this kind of
situation by postulating it as an axiom:
|*)

Axiom not_lem : forall P : Prop, ~ (P \/ ~ P).

(*|
But then we also have a weaker version (double-negated) of LEM:
|*)

Lemma not_not_lem (P : Prop) : ~ ~ (P \/ ~ P).
Proof.
  intros nlem. apply nlem.
  right. intros p. apply nlem.
  left. exact p.
Qed.

(*| These two facts together would make Coq's logic inconsistent: |*)

Lemma Coq_would_be_inconsistent :
  False.
Proof.
  apply (not_not_lem True). apply not_lem.
Qed.

(*|
Answer (ejgallego)
******************

What you are trying to construct is not the negation of LEM, which
would say "there exists some P such that EM doesn't hold", but the
claim that says that no proposition is decidable, which of course
leads to a trivial inconsistency:
|*)

Reset Initial. (* .none *)
Axiom not_lem : forall P : Prop, ~ (P \/ ~ P).

Goal False.
  now apply (not_lem True); left.

(*|
No need to use the fancy double-negation lemma; as this is obviously
inconsistent [imagine it would hold!]

The "classical" negation of LEM is indeed:
|*)

Reset Initial. (* .none *)
Axiom not_lem : exists P : Prop, ~ (P \/ ~ P).

(*|
and it is not provable [otherwise EM wouldn't be admissible], but you
can assume it safely; however it won't be of much utility for you.
|*)

(*|
Answer (Ember Edison)
*********************

I'm coming from mathoverflow, but I don't have permission to comment
on @Anton Trunov's answer. I think his answer is unjust, or at least
incomplete: he hides the following "folklore":

Coq + Impredicative Set + Weak Excluded-middle -> False

This folklore is a variation of the following facts:

1. proof irrelevance + large elimination -> false
2. Coq + Impredicative Set is canonical, soundness, strong
   normalization, so it is consistent.

Coq + Impredicative Set is the old version of Coq. I think this at
least shows that the defense of the LEM based on double negative
translation is not that convincing.

If you want to get information about the solutions, you can get it
from here https://github.com/FStarLang/FStar/issues/360

On the other hand, you may be interested in the story of how
Coq-HoTT+UA went against LEM∞...

----

Ok, let's have some solutions.

1. use command-line flag ``-impredicative-set``, or the install old
   version (<8.0) of coq.
2. `excluded-middle -> proof-irrelevance
   <https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html>`__
3. `proof-irrelevance -> False
   <https://github.com/coq-contribs/paradoxes/blob/master/Hurkens_Set.v>`__

Or you can work with standard coq + coq-hott.

1. install coq-hott
2. `Univalence + Global Excluded-middle (LEM∞) -> False
   <https://github.com/lwoo1999/SomeAgdaCode/blob/master/hottstuff.agda>`__

It is not recommended that you directly click on the code in question
without grasping the specific concept.

I skipped a lot about meta-theoretic implementations, such as
Univalence not being computable in Coq-HoTT but only in Agda-CuTT,
such as the consistency proof for Coq+Impredicative Set/Coq-HoTT.

However, metatheoretical considerations are important. If we just want
to get an Anti-LEM model and don't care about metatheory, then we can
use "Boolean-valued forcing" in coq to wreak havoc on things that only
LEM can introduce, such as "every function about real set is
continuous", Dedekind infinite...

But this answer ends there.
|*)
