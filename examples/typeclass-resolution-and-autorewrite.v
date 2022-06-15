(*|
####################################
Typeclass resolution and autorewrite
####################################

:Link: https://stackoverflow.com/q/39335437
|*)

(*|
Question
********

I have a base of rewrite lemmas. Some of them are parameterized by
typeclasses. When applying a lemma, it is important that the rewrite
fails when the typeclass cannot be automatically resolved by Coq. The
only way I have found to get this behaviour is to declare most of the
parameters implicit.
|*)

Class T (t : Type) : Type.
Instance T1 : T nat.
Qed.
Instance T2 : forall {A1 A2 : Type} {t1 : T A1} {t2 : T A2}, T (A1 * A2).
Qed.

Definition f {A : Type} (x : A) := x.

Lemma f_eq : forall {A : Type} (t : T A) (x : A), f x = x.
Proof.
  reflexivity.
Qed.

Lemma test1 : f (0, 1) = (0, 1).
Proof.
  rewrite f_eq.
  (* a subgoal T (nat * nat) is generated, which should have been
     resolved directly *)
Abort.

Lemma test2 : f (0, true) = (0, true).
Proof.
  rewrite f_eq.
  (* a subgoal T (nat * bool) is generated, while it should have
     failed *)
Abort.

Arguments f_eq {_ _} _.

Lemma test1 : f (0, 1) = (0, 1).
Proof.
  rewrite f_eq.
  reflexivity. (* OK *)
Qed.

Lemma test2 : f (0, true) = (0, true).
Proof.
  Fail rewrite f_eq. (* fails as expected *)
Abort.

(*|
Then I want to add my lemmas to a rewrite database, but the lemma
added to the database is already specialized.
|*)

Hint Rewrite f_eq : my_db.

Print Rewrite HintDb my_db. (* .unfold *)

(*|
How can I add my lemmas to a rewrite database and get the proper
behaviour in terms of typeclass resolution of their arguments?

EDIT: there is an option ``Set Typeclass Resolution After Apply.``
that seems to enable the behaviour that I expect, but only for
``apply``, not ``rewrite``. The corresponding commit gives the
following description:

    Add an option to solve typeclass goals generated by apply which
    can't be catched otherwise due to the discrepancy between evars
    and metas.
|*)

(*|
Answer (ejgallego)
******************

One possible solution is to use ssreflect's rewrite (this will fix the
first part of the problem) and replace the hint db by multi-rewrite
rules. That is to say:
|*)

Reset Initial. (* .none *)
From mathcomp Require Import ssreflect.

Class T (t : Type) : Type.
Instance T1 : T nat.
Qed.
Instance T2 : forall {A1 A2 : Type} {t1 : T A1} {t2 : T A2}, T (A1 * A2).
Qed.

Definition f {A : Type} (x : A) := x.

Lemma f_eq : forall {A : Type} (t : T A) (x : A), f x = x.
Proof. by []. Qed.

(* Add more lemmas as needed *)
Definition my_db A := (@f_eq A, @f_eq A).

Lemma test1 : f (0, 1) = (0, 1).
Proof. by rewrite my_db. Qed.

Lemma test2 : f (0, true) = (0, true).
Proof.
  Fail rewrite f_eq.
Abort.

(*|
Answer (Anton Trunov)
*********************

Here is a workaround. First, we add the *generalized* lemma, but we
tell the ``autorewrite`` tactic to use the tactic ``exact _`` to solve
the secondary goal of resolving the necessary typeclass instance.

.. coq:: none
|*)

Reset Initial.

Class T (t : Type) : Type.
Instance T1 : T nat.
Qed.
Instance T2 : forall {A1 A2 : Type} {t1 : T A1} {t2 : T A2}, T (A1 * A2).
Qed.

Definition f {A : Type} (x : A) := x.

Lemma f_eq : forall {A : Type} (t : T A) (x : A), f x = x.
Proof. reflexivity. Qed.

(*||*)

Hint Rewrite @f_eq using (exact _) : my_db.
Print Rewrite HintDb my_db. (* .unfold *)

(*|
Then you can keep rewriting with ``rewrite`` as you've shown in the
body of your question, or you can use your database:
|*)

Lemma test1' : f (0, 1) = (0, 1).
Proof.
  autorewrite with my_db. reflexivity.
Qed.

Lemma test2 : f (0, true) = (0, true).
Proof.
  autorewrite with my_db.
  (* does nothing: no rewrites, no error messages *)
Abort.

(*|
Notice that when we use ``exact _`` Coq does *not* generate new
instances of the form ``Build_T (nat * bool)`` in the last case, as it
would do if we used ``reflexivity`` instead. Here is an example of
what I mean by that. If we started with this hint
|*)

Hint Rewrite @f_eq using reflexivity : my_db.

(*| we could prove ``test2`` this way |*)

Lemma test2 : f (0, true) = (0, true).
Proof.
  autorewrite with my_db. reflexivity.
Qed.

(*|
But if we look at it using ``Set Printing All. Print test2.`` we will
see that Coq constructed a *new instance* of ``T``: ``(Build_T (prod
nat bool))`` which I think goes against your goal -- it seems you'd
prefer Coq to infer an already existing instance of ``T`` if it's
possible at all or fail in some way.

We can repeat the same thing manually:
|*)

Lemma test2' : f (0, true) = (0, true).
Proof.
  rewrite @f_eq.
  - reflexivity.
  - exact (Build_T (nat * bool)). (* `exact _` won't work *)
Qed.