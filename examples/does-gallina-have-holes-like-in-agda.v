(*|
Does Gallina have holes like in Agda?
=====================================

:Link: https://stackoverflow.com/questions/60662078/does-gallina-have-holes-like-in-agda
|*)

(*|
Question
--------

When proving in Coq, it's nice to be able to prove one little piece at
a time, and have Coq help keep track of the obligations.
|*)

Theorem ModusPonens: forall (A B : Prop), ((A -> B) /\ A) -> B.
Proof.
  intros A B [H1 H2].
  apply H1. (* .unfold *)
  exact H2. (* .none *)
Qed. (* .none *)

(*|
At this point I can see the proof state to know what is required to
finish the proof.

But when writing Gallina, do we have to solve the whole thing in one
bang, or make lots of little helper functions? I'd love to be able to
put use a question mark to ask Coq what it's looking for:

.. coq:: fails
|*)

Fail Definition ModusPonens' :=
  fun (A B : Prop) (H : (A -> B) /\ A) =>
    match H with
    | conj H1 H2 => H1 _ (* hole of type B *)
    end.

(*|
It really seems like Coq should be able to do this, because I can even
put ltac in there and Coq will find what it needs:
|*)

Definition ModusPonens' := fun (A B : Prop) (H : (A -> B) /\ A) =>
  match H with
    | conj H1 H2 => H1 ltac:(assumption)
  end.

(*|
If Coq is smart enough to finish writing the definition for me, it's
probably smart enough to tell me what I need to write in order to
finish the function myself, at least in simple cases like this.

So how do I do this? Does Coq have this kind of feature?
|*)

(*|
Answer (larsr)
--------------

You can use ``refine`` for this. You can write underscores which will
turn into obligations for you to solve later.
|*)

Reset ModusPonens. (* .none *)
Definition ModusPonens: forall (A B : Prop), ((A -> B) /\ A) -> B.
  refine (fun A B H =>
            match H with
            | conj H1 H2 => H1 _ (* hole of type A *)
            end).

(*|
Now your goal is to provide an ``A``. This can be discharged with
|*)

  exact H2. Defined.

(*|
Answer (Li-yao Xia)
-------------------

Use an underscore

.. coq:: unfold fails
|*)

Fail Definition ModusPonens' :=
  fun (A B : Prop) (H : (A -> B) /\ A) =>
    match H with
    | conj H1 H2 => H1 _ (* hole of type A *)
    end.

(*| or use ``Program`` |*)

Require Import Program.
Obligation Tactic := idtac.
(* By default Program tries to be smart and solve simple obligations
   automatically. This commands disables it. *)

Program Definition ModusPonens' :=
  fun (A B : Prop) (H : (A -> B) /\ A) =>
    match H with
    | conj H1 H2 => H1 _ (* hole of type A *)
    end.

Next Obligation. intros. (* See the type of the hole *) (* .unfold *)
Abort. (* .none *)
