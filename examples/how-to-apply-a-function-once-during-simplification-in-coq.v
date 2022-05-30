(*|
##########################################################
How to apply a function once during simplification in Coq?
##########################################################

:Link: https://stackoverflow.com/q/33060802
|*)

(*|
Question
********

From what I understand, function calls in Coq are opaque. Sometimes, I
need to use ``unfold`` to apply it and then ``fold`` to turn the
function definition/body back to its name. This is often tedious. My
question is, is there an easier way to let apply a specific instance
of a function call?

As a minimal example, for a list ``l``, to prove right-appending
``[]`` does not change ``l``:
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Theorem nil_right_app : forall {Y} (l : list Y), l ++ [] = l.
Proof.
  induction l.
  - reflexivity.

(*| This leaves: |*)

  - Show. (* .unfold .messages *)

(*|
Now, I need to apply the definition of ``++`` (i.e. ``app``) once
(pretending there are other ``++`` in the goal which I don't want to
apply/expand). Currently, the only way I know to implement this one
time application is to first unfold ``++`` and then fold it:
|*)

    unfold app at 1. fold (app l []).

(*| giving: |*)

    Show. (* .unfold .messages *)

(*|
But this is inconvenient as I have to figure out the form of the term
to use in ``fold``. I did the computation, not Coq. My question boils
down to:

Is there a simpler way to implement this one-time function application
to the same effect?

----

**A:** All Coq's definition are not opaque, but there are ways to
prevent Coq from unfolding a definition automatically (e.g. using
``Qed`` instead of ``Defined`` when defining a function using
tactics).
|*)

(*|
Answer
******

You can use ``simpl``, ``compute`` or ``vm_compute`` if you want to
ask Coq to perform some computation for you. If the definition of the
function is ``Opaque``, the above solution will fail, but you could
first prove a rewriting lemma such as:

.. code-block:: coq

    forall (A : Type) (a : A) (l1 l2 : list A), (a :: l1) ++ l2 = a :: (l1 ++ l2).


using your technique, and then ``rewrite`` with it when necessary.

Here is an example using ``simpl``:
|*)

Reset nil_right_app. (* .none *)
Theorem nil_right_app : forall {Y} (l : list Y), l ++ nil = l.
Proof.
  (* solve the first case directly *)
  intros Y. induction l as [| hd tl hi]; [reflexivity |].
  simpl app. (* or simply "simpl." *)
  rewrite hi. reflexivity.
Qed.

(*|
To answer your comment, I don't know how to tell ``cbv`` or
``compute`` to only compute a certain symbol. Note that in your case,
they seem to compute too eagerly and ``simpl`` works better.
|*)
