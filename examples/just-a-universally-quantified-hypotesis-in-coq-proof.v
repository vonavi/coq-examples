(*|
####################################################
Just a universally quantified hypotesis in Coq proof
####################################################

:Link: https://stackoverflow.com/q/19053778
|*)

(*|
Question
********

Another hard goal (for me, of course) is the following:
|*)

Goal ~(forall P Q : nat -> Prop,
          (exists x, P x) /\ (exists x, Q x) -> (exists x, P x /\ Q x)).
Proof.
Abort. (* .none *)

(*|
I absolutely have no idea of what could I do. If I introduce
something, I get a universal quantifier in the hypotesis, and then I
can't do anything with it.

I suppose that it exists a standard way for managing such kind of
situations, but I was not able to find it out.
|*)

(*|
Answer (Ptival)
***************

To progress in that proof, you will have to exhibit an instance of
``P`` and an instance of ``Q`` such that your hypothesis produces a
contradiction.

A simple way to go is to use:

.. code-block:: coq

    P : fun x => x = 0
    Q : fun x => x = 1

In order to work with the hypothesis introduced, you might want to use
the tactic ``specialize``:
|*)

Goal ~(forall P Q : nat -> Prop,
          (exists x, P x) /\ (exists x, Q x) -> (exists x, P x /\ Q x)).
Proof.
  intro H.
  specialize (H (fun x => x = 0) (fun x => x = 1)).

(*|
It allows you to apply one of your hypothesis on some input (when the
hypothesis is a function). From now on, you should be able to derive a
contradiction easily.

Alternatively to ``specialize``, you can also do:
|*)

  Undo. (* .none *)
  pose proof (H (fun x => x = 0) (fun x => x = 1)) as Happlied.
Abort. (* .none *)

(*|
Which will conserve ``H`` and give you another term ``Happlied`` (you
choose the name) for the application.
|*)

(*|
Answer (Matteo Zanchi)
**********************

The answer of Ptival did the trick. Here is the code of the complete
proof:
|*)

Goal ~(forall P Q : nat -> Prop,
          (exists x, P x) /\ (exists x, Q x) -> (exists x, P x /\ Q x)).
Proof.
  unfold not. intros.
  destruct (H (fun x => x = 0) (fun x => x = 1)).
  - split.
    + exists 0. reflexivity.
    + exists 1. reflexivity.
  - destruct H0. rewrite H0 in H1. inversion H1.
Qed.
