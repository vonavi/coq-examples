(*|
###############################################
Dealing with let-in expressions in current goal
###############################################

:Link: https://stackoverflow.com/q/48278491
|*)

(*|
Question
********

I got stuck while doing some coq proofs around the ``state`` monad.
Concretely, I've simplified the situation to this proof:
|*)

Definition my_call {A B C} (f : A -> B * C) (a : A) : B * C :=
  let (b, c) := f a in (b, c).

Lemma mycall_is_call : forall {A B C} (f : A -> B * C) (a : A),
    my_call f a = f a.
Proof.
  intros A B C f a. unfold my_call.
  (* stuck! *)

(*| The resulting goal after invoking ``unfold`` is |*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
If I'm not wrong, both sides of the equality should be exactly the
same, but I don't know how to show it from here. Any help?

--

As a side note, I've seen that coq automatically applies the
simplification when no product types are involved in the result of the
function:
|*)

Definition my_call' {A B : Type} (f : A -> B) (a : A) : B :=
  let b := f a in b.

Lemma my_call_is_call' : forall A B (f : A -> B) (a : A),
    my_call' f a = f a.
Proof.
  intros A B f a. unfold my_call'. reflexivity.
Qed.

(*|
Answer
******

It's easy to see what you need to do next, once you recall that

.. code-block:: coq

    let (b, c) := f a in (b, c)

is syntactic sugar for

.. code-block:: coq

    match f a with (b, c) => (b, c) end

This means you need to destruct on ``f a`` to finish the proof:
|*)

Lemma mycall_is_call {A B C} (f : A -> B * C) a :
  my_call f a = f a.
Proof.
  unfold my_call. now destruct (f a).
Qed.

(*|
----

**A:** Note that you can ``Set Printing All`` to make the syntactic
sugar go away.

**A:** With pairs defined with primitive projections (as `here
<https://stackoverflow.com/a/48296323/2747511>`__), we can prove
``mycall_is_call`` lemma using just ``reflexivity``.
|*)
