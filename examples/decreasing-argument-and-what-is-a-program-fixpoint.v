(*|
########################################################
Decreasing argument (and what is a ``Program Fixpoint``)
########################################################

:Link: https://stackoverflow.com/q/47816742
|*)

(*|
Question
********

Consider the following fixpoint:
|*)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive my_type: Type:=
| Left: my_type
| Right: my_type.

Fail Fixpoint decrease (which : my_type) (left right : list my_type) :
  list my_type :=
  match which with
  | Left =>
      match left with
      | [] => []
      | a::tl => decrease a tl right
      end
  | Right =>
      match right with
      | [] => []
      | a::tl => decrease a left tl
      end
  end. (* .fails *)

(*|
Coq rejects the following fixpoint because it can not guess the
decreasing fixpoint (sometimes the ``left`` list looses its head,
sometimes it is the ``right`` one).

This `answer
<https://stackoverflow.com/questions/33302526/well-founded-recursion-in-coq>`__
shows that one can solve this by using a ``Program Fixpoint`` and
specifying a ``{measure ((length left)+(length right))}``.

My questions are:

- What is the difference between a regular ``Fixpoint`` and a
  ``Program Fixpoint``?
- Is it possible to explicit the decreasing argument in a regular
  ``Fixpoint``?
- What is the ``Next Obligation`` goal?
|*)

(*|
Answer
******

- The ``Fixpoint`` command in Coq constructs a recursive function
  using Coq's primitive ``fix``, which checks for structural recursion
  to ensure termination. This is the only recursion in Coq, and all
  other techniques ultimately desugar to a ``fix`` of some sort.

  ``Program Fixpoint`` is a feature of `Program
  <https://coq.inria.fr/refman/program.html>`__, which allows writing
  definitions in a slightly extended language that are then compiled
  into Coq definitions. ``Program Fixpoint`` accepts any recursive
  function, generates an appropriate proof obligation that shows the
  function terminates (by decreasing some measure of its arguments on
  each recursive subcall), and then packages up the definition and
  termination proof into a Coq definition that structurally decreases
  an argument. If that sounds magical it basically is, but `CPDT
  <http://adam.chlipala.net/cpdt/html/GeneralRec.html>`__ gives a good
  explanation of how to do this kind of encoding.

- Yes, you can add a ``{struct arg}`` annotation to explicitly specify
  *which argument is structurally decreasing*: ``Fixpoint decrease
  (which: my_type) (left right: list my_type) {struct right} : list
  my_type``. This doesn't help for your example, since your function
  doesn't in general structurally decrease either argument. All
  primitive ``fix`` constructs have a ``struct`` annotation, but Coq
  can usually infer it automatically when you write a ``Fixpoint``.
  For example, here's ``Nat.add``:
|*)

  Print Nat.add. (* .unfold .messages *)

(*|
- You get two types of goals from ``Next Obligation`` with ``Program
  Fixpoint``: first that each subcall has a smaller argument (using
  ``measure``, "smaller" is defined using < on nats), and second, that
  the "smaller" relation is well-founded; this is, it has no
  infinitely descending sequences of smaller and smaller objects. I'm
  not sure why ``Program Fixpoint`` doesn't do this automatically for
  ``Nat.lt``, given that it should know the relevant theorem. Note
  that ``Program`` has more features than just more general recursion,
  so it can generate other goals related to those features as well,
  depending on the definition you write.
|*)
