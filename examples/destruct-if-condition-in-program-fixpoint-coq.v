(*|
#############################################
Destruct if condition in program fixpoint Coq
#############################################

:Link: https://stackoverflow.com/q/51017689
|*)

(*|
Question
********

I want to proof the factor function correctness in `Use proof of if
expression = true in then part coq
<https://stackoverflow.com/questions/51012942/use-proof-of-if-expression-true-in-then-part-coq>`__
|*)

Require Import ZArith Znumtheory.

Local Open Scope Z_scope.

Require Coq.Program.Wf.
Require Import Coq.micromega.Lia.

Lemma divgt0 (a b : Z) (agt0 : 0 < a) (bgt1 : 1 < b) (dvd : (b | a)) :
  0 < a / b.
Proof.
  now apply Zdivide_Zdiv_lt_pos.
Qed.

Program Fixpoint factor (a b : Z) (agt0 : 0 < a) (bgt1 : 1 < b)
        {measure (Z.abs_nat a)} :=
  if Zdivide_dec b a
  then 1 + factor (a / b) b (divgt0 a b agt0 bgt1 _)  bgt1
  else 0.
Next Obligation.
  assert (0 < a / b < a).
  - now apply Zdivide_Zdiv_lt_pos.
  - apply Zabs_nat_lt. lia.
Qed.

Lemma factor_div (a b : Z) (agt0 : 0 < a) (bgt1 : 1 < b) :
  (b ^ (factor a b agt0 bgt1) | a).
Proof.
  unfold factor.

(*|
after ``unfold`` I expected see a ``if`` and destruct its condition,
but now I see this:
|*)
  Show. (* .unfold .messages *)
Abort. (* .none *)

(*| How I can complete the proof? |*)

(*|
Answer
******

``Program`` gives you terms that are difficult to work with, so you
should prove a lemma that ``factor`` is equal to its body, and then
rewrite with that, instead of unfolding. (I used ``match`` instead of
``if`` to get hold of the ``dvd`` proof term.)
|*)

Lemma factor_lemma a b agt0 bgt1:
  factor a b agt0 bgt1 =
  match Zdivide_dec b a with
  | left dvd => 1 + factor (a / b) b (divgt0 a b agt0 bgt1 dvd) bgt1
  | right notdvd => 0
  end.
Proof.
  unfold factor at 1. unfold factor_func.
  rewrite Program.Wf.Fix_eq; fold factor_func.
  - reflexivity.
  - intros. destruct Zdivide_dec; auto. congruence.
Qed.

(*|
When you unfold and rewrite with ``Fix_eq`` you get such a horrible
goal term to look at that it's best to fold it quickly! :-) It can be
handled with ``reflexivity`` or ``auto`` anyway.

The second goal typically requires algebraic manipulation with ``lia``
or similar to show that the LHS equals RHS, but in this case it was
sufficient with ``congruence``.

How did I know to use ``Fix_eq``? When I unfolded ``factor_func`` I
saw it contained ``Wf.Fix_sub``, so I searched for lemmas with
``Search (Wf.Fix_sub).`` and found a few.

Now you should continue your proof by rewriting with the lemma:
|*)

Lemma factor_div (a b : Z) (agt0 : 0 < a) (bgt1 : 1 < b) :
  (b ^ (factor a b agt0 bgt1) | a).
Proof.
  rewrite factor_lemma. destruct Zdivide_dec.
  2: now rewrite Z.pow_0_r; apply Z.divide_1_l.

(*| Now your goal state is |*)
  Show. (* .unfold .messages *)
Abort. (* .none *)

(*| which probably makes more sense. |*)
