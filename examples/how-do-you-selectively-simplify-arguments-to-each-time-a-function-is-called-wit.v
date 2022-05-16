(*|
####################################################################################################################
How do you selectively simplify arguments to each time a function is called, without evaluating the function itself?
####################################################################################################################

:Link: https://stackoverflow.com/q/41404337
|*)

(*|
Question
********

To make a contrived but illustrative example,
|*)

(* fix so simpl will automatically unfold. *)
Definition double := fix f n := 2*n.

Theorem contrived n : double (2 + n) = 2 + double (1 + n).

(*|
Now, I only want to simplify the arguments to double, and not any part
outside of it. (For example, because the rest has already carefully
been put into the correct form.)
|*)

  simpl.
  Show. (* .unfold .messages *)

(*|
This converted the outside ``(2 + ...)`` to ``(S (S ...))`` as well as
unfolding double.

I can match one of them by doing:
|*)

  Undo. (* .none *)
  match goal with | |- (double ?A) = _ => simpl A end.
  Show. (* .unfold .messages *)

(*|
How do I say that I want to simplify all of them? That is, I want to
get
|*)
  enough (double (S (S n)) = 2 + double (S n)) by auto. (* .none *)
  Show. (* .unfold .messages *)

(*|
without having to put a separate pattern for each call to ``double``.

I can simplify except for double itself with
|*)

  Undo. (* .none *)
  remember double as x. simpl. subst x.
  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
Answer (Anton Trunov)
*********************

Opaque/Transparent approach
===========================

Combining the results of `this answer
<https://stackoverflow.com/a/39363591/2747511>`__ and `this one
<https://stackoverflow.com/a/39363591/2747511>`__, we get the
following solution:
|*)

Theorem contrived n : double (2 + n) = 2 + double (1 + n). (* .none *)
  Opaque double.
  simpl (double _).
  Transparent double.
Abort. (* .none *)

(*|
We use the pattern capability of ``simpl`` to narrow down its "action
domain", and ``Opaque``/``Transparent`` to forbid (allow resp.)
unfolding of ``double``.

Custom tactic approach
======================

We can also define a custom tactic for simplifying arguments:
|*)

(* simplifies the first argument of a function *)
Ltac simpl_arg_of function :=
  repeat multimatch goal with
         | |- context [function ?A] =>
             let A' := eval cbn -[function] in A in
               change A with A'
         end.

(*|
That ``let A' := ...`` construction is needed to protect nested
functions from simplification. Here is a simple test:
|*)

Fact test n :
  82 + double (2 + n) = double (1 + double (1 + 20)) + double (1 * n).
Proof.
  simpl_arg_of double.

(*| The above results in |*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
Had we used something like ``context [function ?A] => simpl A`` in the
definition of ``simpl_arg_of``, we would've gotten

.. coq:: none
|*)

Reset simpl_arg_of.

(* simplifies the first argument of a function *)
Ltac simpl_arg_of function :=
  repeat multimatch goal with
         | |- context [function ?A] => simpl A
         end.

Fact test n :
  82 + double (2 + n) = double (1 + double (1 + 20)) + double (1 * n).
Proof.
  simpl_arg_of double.

(*||*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
instead.

Arguments directive approach
============================

As suggested by @eponier in comments, we can take advantage of yet
another form of ``simpl`` -- ``simpl <qualid>``, which the `manual
<https://coq.inria.fr/distrib/current/refman/proofs/writing-proofs/equality.html#coq:tacn.simpl>`__
defines as:

    This applies ``simpl`` only to the applicative subterms whose head
    occurrence is the unfoldable constant *qualid* (the constant can
    be referred to by its notation using string if such a notation
    exists).

The ``Opaque``/``Transparent`` approach doesn't work with it, however
we can block unfolding of ``double`` using the ``Arguments``
directive:
|*)

Theorem contrived n : double (2 + n) = 2 + double (1 + n). (* .none *)
  Arguments double : simpl never.
  simpl double.
  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
Answer (ejgallego)
******************

You may find the ssreflect pattern selection language and rewrite
mechanism useful here. For instance, you can have a finer grained
control with patterns + the simpl operator ``/=``:
|*)

Reset Initial. (* .none *)
From mathcomp Require Import ssreflect.
Definition double := fix f n := 2*n.
Theorem contrived n : double (2 + n) = 2 + double (1 + n).
  rewrite ![_ + n] /=.

(*| Will display: |*)

  Show. (* .unfold .messages *)

(*| You can also use anonymous rewrite rules: |*)

  Undo. (* .none *)
  rewrite (_ : double (2 + n) = 2 + double (1 + n)) //.
Abort. (* .none *)

(*| I would personally factor the rewrite in smaller lemmas: |*)

Lemma doubleE n : double n = n + n.
Proof. by elim: n => //= n ihn; rewrite -!plus_n_Sm -plus_n_O. Qed.

Lemma doubleS n : double (1 + n) = 2 + double n.
Proof. by rewrite !doubleE /= -plus_n_Sm. Qed.

Theorem contrived n : double (1 + n) = 2 + double n.
  now rewrite doubleS.
Qed.
