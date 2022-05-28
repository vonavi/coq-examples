(*|
#############################
Proof by case analysis in Coq
#############################

:Link: https://stackoverflow.com/q/33856689
|*)

(*|
Question
********

I am trying to prove a Proposition about the following function:

.. coq:: none
|*)

Require Import PeanoNat.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.

Definition menos m n := m - n.

(*||*)

Program Fixpoint division (m : nat) (n : nat) {measure m} : nat :=
  match 0 <? n with
  | false => 0
  | true => match n <=? m with
            | false => 0
            | true => S (division (menos m n) n)
            end
  end.
Next Obligation. (* .none *) Admitted. (* .none *)
Next Obligation. (* .none *) Admitted. (* .none *)

(*|
``menos`` is natural subtraction.

I am trying to prove some fact involving division. I wrote down an
informal proof were I first consider a case analysis in ``lt_nat 0 n``
and then in the case when ``lt_nat`` is true a further case analysis
in ``leq_nat n m``. This is in order to reduce the definition of
division.

However I can not find how to express this case analysis in Coq. I
tried with ``destruct (leq_nat n m)`` but it does nothing. I am
expecting Coq to generate two subgoals: one where I need to prove my
proposition assuming ``leq_nat n m = false`` and one assuming
``leq_nat n m = true``.

Furthermore, I can not unfold the definition of division in my proof!
When I try ``unfold division`` I get: ``division_func (existT (fun _ :
nat => nat) m n)``.

How can I perfom case analysis in ``leq_nat n m``? Why is it that I
can not unfold the definition of division as I usually do with other
functions?
|*)

(*|
Answer
******

Everything is more complicated than usual because of ``Program
Fixpoint``, which does not define your function as you would expect
with a classic ``Fixpoint``, since it needs to find a structurally
recursive way of defining it. What ``division`` really is, is hidden
in ``division_func``.

Therefore, to manipulate your function, you need to prove basic
lemmas, including the one stating that your function can be replaced
by its body.
|*)

Lemma division_eq : forall m n,
    division m n = match 0 <? n with
                   | false => 0
                   | true => match n <=? m with
                             | false => 0
                             | true => S (division (menos m n) n)
                             end
                   end.

(*|
Now, the question is how to prove this result. Here is the only
solution I know, which I consider really unsatisfying.

I use the tactic ``fix_sub_eq`` located in ``Program.Wf``, or
``fix_sub_eq_ext`` in ``Program.Wf.WfExtensionality``.

This gives something like:
|*)

Proof.
  intros.
  unfold division. unfold division_func at 1.
  rewrite fix_sub_eq. repeat fold division_func.
  - simpl. destruct (Nat.ltb 0 n) eqn:H.
    destruct (Nat.leb n m) eqn:H0.
    + reflexivity.
    + reflexivity.
    + reflexivity.

(*|
But the second goal is quite complicated. The easy and general way of
solving it is to use the axioms ``proof_irrelevance`` and
``functional_extensionality``. It should be possible to prove this
particular subgoal without any axioms, but I have not found the right
way to do it. Instead of manually applying the axioms, you can use the
second tactic ``fix_sub_eq_ext`` which calls them directly, leaving
you a single goal.
|*)

      Restart. (* .none *)
Proof.
  intros.
  unfold division. unfold division_func at 1.
  rewrite WfExtensionality.fix_sub_eq_ext. repeat fold division_func.
  simpl. destruct (Nat.ltb 0 n) eqn:H.
  destruct (Nat.leb n m) eqn:H0.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(*|
I have not found a better way to use ``Program Fixpoint``, that's why
I prefer using ``Function``, which has other defaults, but generates
directly the equation lemma.
|*)

Reset division. (* .none *)
Require Recdef.
Function division (m : nat) (n : nat) {measure (fun n => n) m} : nat :=
  match 0 <? n with
  | false => 0
  | true => match n <=? m with
            | false => 0
            | true => S (division (menos m n) n)
            end
  end.
Proof.
  intros m n. revert m. induction n; intros.
  - discriminate teq.
  - destruct m.
    + discriminate teq0.
    + simpl. destruct n.
      * destruct m; apply le_n.
      * transitivity m.
        -- apply IHn.
           ++ reflexivity.
           ++ assumption.
        -- apply le_n.
Qed.

Check division_equation.

(*|
Now you have the equation lemma, you can rewrite with it and reason as
usual.

About your problem with ``destruct``, ``destruct`` does not unfold the
definitions. Therefore, if you have no occurrences of the term you're
destructing in your goal or any of the hypotheses, ``destruct`` will
not do anything interesting, unless you save the equation it produces.
You can use ``destruct ... eqn:H`` for this purpose. I did not know
``case_eq`` but it seems to do the same thing.
|*)
