(*|
##################################
renaming part of hypothesis in Coq
##################################

:Link: https://stackoverflow.com/questions/52350119/renaming-part-of-hypothesis-in-coq
|*)

(*|
Question
********

After destructing ``n`` in my proof, I am stuck at the following:

.. coq:: none
|*)

Require Import List.

Lemma toto (n : nat) (X : Type) (l : list nat) :
  length l = n -> nth_error l n = None.
Proof.
  induction l as [ | h t IHl].
  - case_eq n.
    + simpl. auto.
    + simpl. discriminate.
  - case_eq n.
    + simpl. discriminate.
    + intros n' E. simpl.
      intros E'. injection E'. clear E'. intros H'.

(*||*)

      Show 1. (* .unfold .messages *)
Abort. (* .none *)

(*|
I want to rewrite using ``IHl``, but that is not possible. How do I
compose ``IHl`` and ``H'`` to make sense and prove this theorem?
|*)

(*|
Answer (Yves)
*************

I am just trying to elaborate on @Arthur answer.

I was able to reproduce your goal with the following script:
|*)

Require Import List.

Lemma toto (n : nat) (X : Type) (l : list nat) :
  length l = n -> nth_error l n = None.
Proof.
  induction l as [ | h t IHl].
  - case_eq n.
    + simpl. auto.
    + simpl. discriminate.
  - case_eq n.
    + simpl. discriminate.
    + intros n' E. simpl.
      intros E'. injection E'. clear E'. intros H'.

(*|
and I agree that this goal cannot be proved. Now, if you instead start
your proof with the following text (the ``Proof`` and ``induction``
lines have to be replaced), it will be provable (I checked).
|*)

      Restart.
      revert n.
      induction l as [ | h t IHl]; intros n.

(*|
The difference is that the induction hypothesis now has the following
statement.
|*)

      admit. (* .none *) Check IHl. (* .unfold .messages *)

(*|
What happened? In the first (faulty) variant, you attempt to prove a
statement for all lists whose length is equal to a precise ``n``,
because ``n`` is fixed before you start the proof by induction. In the
second (correct) variant, you attempt to prove a statement for all
lists ``l``, and this statement accepts any ``n`` as long as ``length
l = n``.

In the first variant, ``n`` is fixed and the equality ``length l = n``
restricts ``l`` to be among those that have length precisely ``n``. In
the second case, ``l`` is chosen first, and ``n`` is not fixed, but
the equality ``length l = n`` restricts ``n`` to follow the length of
``l``.

This is called "loading the induction" because the statement ``forall
n, length l = n -> nth_error l n = None`` is stronger (it is loaded)
than the statement that you attempt to prove in the first variant
(just for one specific ``n``), but surprisingly it is easier to prove.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

You cannot, because your induction hypothesis is not general enough.
Here is a statement that should be easier to prove:

.. code-block:: coq

    forall (X : Type) (t : list X), nth_error t (length t) = None
|*)
