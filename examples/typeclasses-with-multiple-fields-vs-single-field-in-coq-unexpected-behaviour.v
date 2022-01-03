(*|
##################################################################################################
Typeclasses with multiple fields vs. single field in Coq / Unexpected behaviour of Compute command
##################################################################################################

:Link: https://stackoverflow.com/q/56201202
|*)

(*|
Question
********

I'm studying typeclasses in Coq with the book Software Foundations.

Running the following:
|*)

Class Eq A :=
  {
  eqb: A -> A -> bool;
  }.

Notation "x =? y" := (eqb x y) (at level 70).

Instance eqBool : Eq bool :=
  {
  eqb := fun (b c : bool) =>
           match b, c with
           | true, true => true
           | true, false => false
           | false, true => false
           | false, false => true
           end
  }.

Compute (true =? false). (* .unfold *)

(*|
I get the message as expected. But if I do the following instead,
|*)

Reset Initial. (* .none *)
Class Eq A :=
  {
  eqb: A -> A -> bool;
  eqb_refl: forall (x : A), eqb x x = true;
  }.

Notation "x =? y" := (eqb x y) (at level 70).

#[refine] Instance eqBool : Eq bool :=
  {
  eqb := fun (b c : bool) =>
           match b, c with
           | true, true => true
           | true, false => false
           | false, true => false
           | false, false => true
           end
  }.
Proof.
  intros []; reflexivity.
Qed.

Compute (true =? false). (* .unfold *)

(*|
I don't seem to be able to simplify this expression and not sure what
went wrong and where. How can I define the typeclass above with the
extra hypothesis, and still be able to use the instance i've defined
(i.e get the same message as before)?

Thanks a lot!
|*)

(*|
Answer
******

The ``Qed`` command creates opaque definitions, which are never
unfolded by commands like ``Compute``. You can tell Coq to make only
the proof obligation opaque by using the ``Program Instance`` command:
|*)

Reset Initial. (* .none *)
Require Import Coq.Program.Tactics.

Class Eq A :=
  {
  eqb: A -> A -> bool;
  eqb_refl: forall (x : A), eqb x x = true;
  }.

Notation "x =? y" := (eqb x y) (at level 70).

Program Instance eqBool : Eq bool :=
  {
  eqb := fun (b c : bool) =>
           match b, c with
           | true, true => true
           | true, false => false
           | false, true => false
           | false, false => true
           end
  }.
Next Obligation. now destruct x. Qed.

Compute (true =? false).
