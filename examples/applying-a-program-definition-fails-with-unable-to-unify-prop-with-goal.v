(*|
###########################################################################
Applying a Program Definition fails with "unable to unify Prop with [goal]"
###########################################################################

:Link: https://stackoverflow.com/q/50316390
|*)

(*|
Question
********

In Coq, I showed the associativity of ``append`` on vectors using:
|*)

Require Import Coq.Vectors.VectorDef Coq.micromega.Lia.

Program Definition t_app_assoc v p q r (a : t v p) (b : t v q) (c : t v r) :=
  append (append a b) c = append a (append b c).
Next Obligation. lia. Qed.

(*|
I now want to apply this equality in a proof. Below is the easiest
goal that I would expect to be provable with ``t_app_assoc``. Of
course it can be proven by ``simpl`` - this is just an example.

This ``apply`` fails:
|*)

Goal (append (append (nil nat) (nil _)) (nil _)
      = append (nil _) (append (nil _) (nil _))).
  Fail apply t_app_assoc. (* .fails .unfold .no-goals *)
Abort. (* .none *)

(*|
How can I apply ``t_app_assoc``? Or is there a better way to define
it? I thought I needed a ``Program Definition``, because simply using
a ``Lemma`` leads to a type error because ``t v (p + (q + r))`` and
``t v (p + q + r)`` are not the same to Coq.
|*)

(*|
Answer
******

Prologue
========

I guess what you want to to is to prove that the vector concatenation
is associative and then use that fact as a lemma.

But ``t_app_assoc`` as you define it has the following type:
|*)

Check t_app_assoc. (* .unfold .messages *)

(*| You basically want to use ``:`` instead of ``:=`` as follows. |*)

From Coq Require Import Vector Arith.
Import VectorNotations.
Import EqNotations.                  (* rew notation, see below *)
Require Import Coq.Program.Equality. (* heterogeneous equality *)

Section Append.

  Variable A : Type.
  Variable p q r : nat.
  Variables (a : t A p) (b : t A q) (c : t A r).

  Fail Lemma t_app_assoc :
    append (append a b) c = append a (append b c).

(*|
Unfortunately, we cannot even state a lemma like this using the usual
homogeneous equality.

The left-hand side has the following type:
|*)

  Check append (append a b) c : t A (p + q + r).

(*| whereas the right-hand side is of type |*)

  Check append a (append b c) : t A (p + (q + r)).

(*|
Since ``t A (p + q + r)`` is not the same as ``t A (p + (q + r))`` we
cannot use ``=`` to state the above lemma.

Let me describe some ways of working around this issue:

``rew`` notation
================
|*)

  Lemma t_app_assoc_rew :
    append (append a b) c = rew (plus_assoc _ _ _) in
      append a (append b c).
  Admitted.

(*|
Here we just use the law of associativity of addition for natural
numbers to cast the type of RHS to ``t A (p + q + r)``.

To make it work one needs to ``Import EqNotations.`` before.

``cast`` function
=================

This is a common problem, so the authors of the ``Vector`` library
decided to provide a ``cast`` function with the following type:
|*)

  Check cast. (* .unfold .messages *)

(*|
Let me show how one can use it to prove the law of associativity for
vectors. But let's prove the following auxiliary lemma first:
|*)

  Lemma uncast {X n} {v : Vector.t X n} e :
    cast v e = v.
  Proof. induction v as [|??? IH]; simpl; rewrite ?IH; reflexivity. Qed.

(*| Now we are all set: |*)

  Lemma t_app_assoc_cast :
    append (append a b) c = cast (append a (append b c)) (plus_assoc _ _ _).
  Proof.
    generalize (Nat.add_assoc p q r).
    induction a as [|h p' a' IH]; intros e.
    - now rewrite uncast.
    - simpl. f_equal. now apply IH.
  Qed.

(*|
Heterogeneous equality (a.k.a. John Major equality)
===================================================
|*)

  Lemma t_app_assoc_jmeq :
    append (append a b) c ~= append a (append b c).
  Admitted.

End Append.

(*| If you compare the definition of the homogeneous equality |*)

Print eq. (* .unfold .messages *)

(*| and the definition of heterogeneous equality |*)

Print JMeq. (* .unfold .messages *)

(*|
you will see that with ``JMeq`` the LHS and RHS don't have to be of
the same type and this is why the statement of ``t_app_assoc_jmeq``
looks a bit simpler than the previous ones.

Other approaches to vectors
===========================

See e.g. `this question
<https://stackoverflow.com/q/42302300/2747511>`__ and `this one
<https://stackoverflow.com/q/49477427/2747511>`__; I also find `this
answer <https://stackoverflow.com/a/27640467/2747511>`__ very useful
too.
|*)
