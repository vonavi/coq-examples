(*|
#############################################
How to do cases with an inductive type in Coq
#############################################

:Link: https://stackoverflow.com/q/6823301
|*)

(*|
Question
********

I wan to use the ``destruct`` tactic to prove a statement by cases. I
have read a couple of examples online and I'm confused. Could someone
explain it better?

Here is a small example (there are other ways to solve it but try
using ``destruct``):
|*)

Inductive three := zero | one | two.
Lemma has2b2 : forall a : three, a <> zero /\ a <> one -> a = two.

(*| Now some examples online suggest doing the following: |*)

Proof.
  intros. destruct a.

(*| In which case I get: |*)

  Show. (* .unfold .messages *)

(*|
So, I want to prove that the first two cases are impossible. But the
machine lists them as subgoals and wants me to PROVE them... which is
impossible.

Summary: How to exactly discard the impossible cases?

I have seen some examples using ``inversion`` but I don't understand
the procedure.

Finally, what happens if my lemma depends on several inductive types
and I still want to cover ALL cases?
|*)

(*|
Answer (akoprowski)
*******************

How to discard impossible cases? Well, it's true that the first two
obligations are impossible to prove, but note they have contradicting
assumptions (``zero <> zero`` and ``one <> one``, respectively). So
you will be able to prove those goals with ``tauto`` (there are also
more primitive tactics that will do the trick, if you are interested).

``inversion`` is a more advanced version of destruct. Additional to
'destructing' the inductive, it will sometimes generate some
equalities (that you may need). It itself is a simple version of
``induction``, which will additionally generate an induction
hypothesis for you.

If you have several inductive types in your goal, you can
``destruct``/``invert`` them one by one.

More detailed walk-through:
|*)

Reset Initial. (* .none *)
Inductive three := zero | one | two.

Lemma test : forall a, a <> zero /\ a <> one -> a = two.
Proof.
  intros a H.
  destruct H. (* to get two parts of conjunction *)
  destruct a. (* case analysis on 'a' *)
  (* low-level proof *)
  - compute in H. (* to see through the '<>' notation *)
    elimtype False. (* meaning: assumptions are contradictory, I can
                       prove False from them *)
    apply H. reflexivity.
    (* can as well be handled with more high-level tactics *)
  - firstorder.
    (* the "proper" case *)
  - reflexivity.
Qed.

(*|
Answer (Gilles 'SO- stop being evil')
*************************************

If you see an impossible goal, there are two possibilities: either you
made a mistake in your proof strategy (perhaps your lemma is wrong),
or the hypotheses are contradictory.

If you think the hypotheses are contradictory, you can set the goal to
``False``, to get a little complexity out of the way. ``elimtype
False`` achieves this. Often, you prove ``False`` by proving a
proposition ``P`` and its negation ``~ P``; the tactic ``absurd P``
deduces any goal from ``P`` and ``~ P``. If there's a particular
hypothesis which is contradictory, ``contradict H`` will set the goal
to ``~ H``, or if the hypothesis is a negation ``~ A`` then the goal
will be ``A`` (stronger than ``~ ~ A`` but usually more convenient).
If one particular hypothesis is obviously contradictory,
``contradiction H`` or just ``contradiction`` will prove any goal.

There are many tactics involving hypotheses of inductive types.
Figuring out which one to use is mostly a matter of experience. Here
are the main ones (but you will run into cases not covered here soon):

1. ``destruct`` simply breaks down the hypothesis into several parts.
   It loses information about dependencies and recursion. A typical
   example is ``destruct H`` where ``H`` is a conjunction ``H : A /\
   B``, which splits ``H`` into two independent hypotheses of types
   ``A`` and ``B``; or dually ``destruct H`` where ``H`` is a
   disjunction ``H : A \/ B``, which splits the proof into two
   different subproofs, one with the hypothesis ``A`` and one with the
   hypothesis ``B``.

2. ``case_eq`` is similar to ``destruct``, but retains the connections
   that the hypothesis has with other hypotheses. For example,
   ``destruct n`` where ``n : nat`` breaks the proof into two
   subproofs, one for ``n = 0`` and one for ``n = S m``. If ``n`` is
   used in other hypotheses (i.e. you have a ``H : P n``), you may
   need to remember that the ``n`` you've destructed is the same ``n``
   used in these hypotheses: ``case_eq n`` does this.

3. ``inversion`` performs a case analysis on the type of a hypothesis.
   It is particularly useful when there are dependencies in the type
   of the hypothesis that ``destruct`` would forget. You would
   typically use ``case_eq`` on hypotheses in ``Set`` (where equality
   is relevant) and ``inversion`` on hypotheses in ``Prop`` (which
   have very dependent types). The ``inversion`` tactic leaves a lot
   of equalities behind, and it's often followed by ``subst`` to
   simplify the hypotheses. The ``inversion_clear`` tactic is a simple
   alternative to ``inversion; subst`` but loses a little information.

4. ``induction`` means that you are going to prove the goal by
   induction (= recursion) on the given hypothesis. For example,
   ``induction n`` where ``n : nat`` means that you'll perform integer
   induction and prove the base case (``n`` replaced by ``0``) and the
   inductive case (``n`` replaced by ``m + 1``).

Your example is simple enough that you can prove it as "obvious by
case analysis on ``a``".
|*)

Lemma has2b2 : forall a : three, a <> zero /\ a <> one -> a = two.
Proof. destruct a; tauto. Qed.

(*|
But let's look at the cases generated by the ``destruct`` tactic, i.e.
after just ``intros; destruct a.``. (The case where ``a`` is ``one``
is symmetric; the last case, where ``a`` is ``two``, is obvious by
reflexivity.)

.. coq:: none
|*)

Reset has2b2.

Lemma has2b2 : forall a : three, a <> zero /\ a <> one -> a = two.
Proof.
  intros; destruct a.

(*||*)

  - Show. (* .unfold .messages *)

(*|
The goal looks impossible. We can tell this to Coq, and here it can
spot the contradiction automatically (``zero = zero`` is obvious, and
the rest is a first-order tautology handled by the ``tauto`` tactic).
|*)

    elimtype False. tauto.

(*|
In fact ``tauto`` works even if you don't start by telling Coq not to
worry about the goal and wrote ``tauto`` without the ``elimtype
False`` first (IIRC it didn't in older versions of Coq). You can see
what Coq is doing with the ``tauto`` tactic by writing ``info tauto``.
Coq will tell you what proof script the ``tauto`` tactic generated.
It's not very easy to follow, so let's look at a manual proof of this
case. First, let's split the hypothesis (which is a conjunction) into
two.
|*)

    Undo 2. (* .none *)
    destruct H as [H0 H1].

(*|
We now have two hypotheses, one of which is ``zero <> zero``. This is
clearly false, because it's the negation of ``zero = zero`` which is
clearly true.
|*)

    contradiction H0. reflexivity.

(*|
We can look in even more detail at what the ``contradiction`` tactic
does. (``info contradiction`` would reveal what happens under the
scene, but again it's not novice-friendly). We claim that the goal is
true because the hypotheses are contradictory so we can prove
anything. So let's set the intermediate goal to ``False``.
|*)

    Undo 2. (* .none *)
    assert (F : False).
(*|
Run ``red in H0.`` to see that ``zero <> zero`` is really notation for
``~(zero = zero)`` which in turn is defined as meaning ``zero = zero
-> False``. So ``False`` is the conclusion of ``H0``:
|*)

    + red in H0. apply H0.

(*| And now we need to prove that ``zero = zero``, which is |*)

      reflexivity.

(*|
Now we've proved our assertion of ``False``. What remains is to prove
that ``False`` implies our goal. Well, ``False`` implies any goal,
that's its definition (``False`` is defined as an inductive type with
0 case).
|*)

    + destruct F.
