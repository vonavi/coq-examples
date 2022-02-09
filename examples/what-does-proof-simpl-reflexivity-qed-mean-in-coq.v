(*|
##########################################################
What does ``Proof. simpl. reflexivity. Qed.`` mean in Coq?
##########################################################

:Link: https://stackoverflow.com/q/64246592
|*)

(*|
Question
********

I'm reading the book Software Foundations and got stuck at the very
beginning.

The author defined a boolean type and common operations:
|*)

Inductive bool: Type :=
| true
| false.

Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(*|
So let's say we want to prove the correctness of the ``or`` function.
The author wrote a test followed by a proof:
|*)

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

(*|
Could someone explain to me what ``simpl. reflexivity.`` mean? Is
there any other way we can prove this simple test?
|*)

(*|
Answer
******

``simpl`` is a tactic evaluating the goal. In your case, after
executing it, the goal will be left to ``true = true``.
``reflexivity`` is a tactic discharging goals of the shape ``x = x``
(in its simplest incarnation). What it does under the hood is to
provide the proof term ``eq_refl : x = x`` as a solution to the
current proof obligation.

Now, there are many ways to achieve this thing that ultimately will
produce the same (rather trivial) proof ``eq_refl`` (try doing ``Print
test_orb1.``). First, the ``simpl`` operation is not needed because
Coq will do some computations when applying a term (in particular when
calling ``reflexivity``). Second, you could obtain the same effect as
``reflexivity`` by calling ``constructor``, ``apply eq_refl`` or
``refine eq_refl``. These are tactics with different goals but that
happen to coincide here.
|*)
