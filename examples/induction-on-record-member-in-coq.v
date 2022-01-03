(*|
##################################
Induction on record member in Coq?
##################################

:Link: https://stackoverflow.com/q/48840413
|*)

(*|
Question
********

Consider a simple example of induction on a record member:
|*)

Record Foo : Type := mkFoo { foo: nat }.

Definition double (f: Foo) : Foo :=
  mkFoo (2 * foo f)%nat.

Theorem double_doubles: forall (f: Foo),
    foo (double f) = (2 * foo f)%nat.
Proof.
  intros.
  induction (foo f).
  (* How do I prevent this loss of information? *)
  (* stuck? *)
Abort.

Theorem double_doubles: forall (f: Foo),
    foo (double f) = (2 * foo f)%nat.
Proof.
  intros. destruct f.
  (* destruct is horrible if your record is large / contains many things *)
  induction foo0.
  - simpl. auto.
  - intros. simpl. auto.
Qed.

(*|
At ``induction (foo f)``, I am stuck with the goal ``foo (double f) =
2 * 0``.

I have somehow lost information that I am perform induction on ``foo
f`` (I have no hypothesis stating that ``foo f = 0``).

However, ``destruct f`` is unsatisfying, because I have ~5 member
records that look very ugly in the hypothesis section when expanded
out.
|*)

(*|
Answer
******

You can use the ``remember`` tactic to give a name to an expression,
yielding a variable that you can analyze inductively. The tactic
generates an equation connecting the variable to the remembered
expression, allowing you to keep track of the information you need.

To illustrate, consider the following proof script.
|*)

Reset Foo. (* .none *)
Record Foo : Type := mkFoo { foo: nat }.

Definition double (f: Foo) : Foo :=
  mkFoo (2 * foo f)%nat.

Theorem double_doubles: forall (f: Foo),
    foo (double f) = (2 * foo f)%nat.
Proof.
  intros. remember (foo f) as n eqn:E.
  revert f E. induction n.

(*| After calling ``remember``, the goal becomes: |*)

  Undo 2. (* .none *) Show 1. (* .unfold .messages *)

(*|
If you do induction on ``n`` directly after ``remember``, it is
possible that you won't be able to complete your proof, because the
induction hypothesis you will get will not be general enough. If you
run into this problem, you might need to generalize some of the
variables that appear in the expression defining ``n``. In the script
above, the call ``revert f E`` puts ``f`` and ``E`` back into the
goal, which solves this problem.

----

**Q:** Thanks! is there a difference between ``revert`` and
``generalize dependent``?

**A:** ``revert`` will give you an error if you try to revert
something that appears in the type of another term or hypothesis in
the context. ``generalize dependent`` will compute all the terms whose
types depend on the generalized one, and will put those back as well.

**Q:** And between ``revert dependent`` and ``generalize dependent``?

**A:** Good question. I do not know.
|*)
