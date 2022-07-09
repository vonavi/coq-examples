(*|
################################################
Understanding the ``intros`` keyword work in Coq
################################################

:Link: https://stackoverflow.com/q/70482977
|*)

(*|
Question
********
|*)

Theorem law_of_contradiction : forall (P Q : Prop), P /\ ~P -> Q.
Proof.
  intros P Q P_and_not_P.
  destruct P_and_not_P as [P_holds not_P].
Abort. (* .none *)

(*|
I'm trying to reaaaally understand the ``intros`` keyword. Let's say
that we want to prove ``P /\ ~P -> Q``. Ok, somehow ``intros P Q``
introduce ``P`` and ``Q``. But what does it mean? Does it recognize
the ``P`` and ``Q`` from the thing to be proven? What about
``P_and_not_P``? What is it? Why for ``P`` and ``Q`` it uses the same
name, but for ``P_and_not_P`` is defining a name?

UPDATE:
=======

It looks like it's matching term by term:
|*)

Theorem modus_tollens : forall (P Q : Prop), (P -> Q) -> ~Q -> ~P.
Proof.
  intro P. intro Q. intro P_implies_Q. intro not_q. intro not_p.

(*| gives |*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
Answer
******

What ``intro A`` (equivalent to ``intros A``) does: if you have a goal
of the form ``forall (P : _), ...``, it renames ``P`` to ``A``,
removes the ``forall`` from the beginning of the goal and puts an
assumption ``A`` into the goal.
|*)

Theorem law_of_contradiction : forall (P Q : Prop), P /\ ~P -> Q. (* .none *)
Proof. (* .none *)
  (* Starting goal *)
  Show. (* .unfold .messages *)
  (* Goal after [intros A] *)
  intros A. (* .none *) Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
If you do ``intros P Q``, by picking the names already in the goal, no
renaming is necessary so there is no change in names.

The other cases of ``intros`` you mention are special cases of that
one behavior.

**Implications** in Coq are quantifications where the assumption is
not named: ``P /\ ~ P -> Q`` is equivalent to ``forall (H : P /\ ~P),
Q``, noting that ``H`` is not used in the body ``Q``. Hence, when you
do ``intros P_and_not_P``, you are renaming ``H``, which is not used
so you don't see a change in the goal. You can disable pretty printing
to see that.
|*)

Unset Printing Notations.
Theorem law_of_contradiction : forall (P Q : Prop), P /\ ~P -> Q. (* .none *)
Proof. (* .none *)
  (* Starting goal; a name that is not used becomes "_" *)
  Show. (* .unfold .messages *)
  (* After [intros P Q R] *)
  intros P Q R. (* .none *) Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
The **negation** of ``P``, denoted ``~P``, is defined as ``P ->
False`` in Coq (this is typical in intuitionistic logic, other logics
might differ). You can see that in action with the tactic ``unfold
not``
|*)

Set Printing Notations. (* .none *)
Theorem modus_tollens : forall (P Q : Prop), (P -> Q) -> ~Q -> ~P. (* .none *)
Proof. (* .none *)
  (* Starting goal *)
  Show. (* .unfold .messages *)
  (* After [unfold not] *)
  unfold not. (* .none *) Show. (* .unfold .messages *)
  (* After [intros P Q R S T] *)
  intros P Q R S T. (* .none *) Show. (* .unfold .messages *)
