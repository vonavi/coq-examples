(*|
################################################################
Proving equivalence of two programs expressed as different types
################################################################

:Link: https://stackoverflow.com/q/68870467
|*)

(*|
Question
********

I understand how to prove equivalence of two programs when they're
represented in the same datatype, from the `first chapter of PL
Foundations
<https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html>`__.
We want to show that they step to the same value.

How does this work when programs are represented as *different* types,
with separate step relations, e.g. when a compiler translates an AST
into an SSA IR which conceptually behaves the same but executes
differently? Another example is a program and transition system, where
there is a correspondence between program reductions and transitions.

Here's what I've tried. There are two languages, ``imp1`` and
``imp2``, with e.g. just a single ``Skip`` command. I figured a good
"evaluation result" would be a (finite, for now) trace of actions, to
allow for concurrency. There are (multi-)step relations defined for
both which allow a finite number of skips.

The problem is that in the final equivalence theorem, the behaviour of
``imp1`` tells me nothing about the behaviour of ``imp2``: given that
the ``imp1`` program takes a ``Skip`` step, I don't know anything
about the next step of ``imp2``.

This feels really silly but what am I missing? Does there need to be
some additional relation mapping single steps of ``imp1`` to those of
``imp2``? This feels too restrictive: what if one step of ``imp1``
corresponds to many steps of ``imp2`` or vice versa? Any other
resources would be welcome!
|*)

From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.

Inductive imp1 : Type :=
| Skip1 : imp1.

Inductive imp2 : Type :=
| Skip2 : imp2.

Inductive action :=
| A.

Inductive step1 : imp1 -> imp1 -> action -> Prop :=
| SkipStep1 : step1 Skip1 Skip1 A.

Inductive step2 : imp2 -> imp2 -> action -> Prop :=
| SkipStep2 : step2 Skip2 Skip2 A.

Definition trace := list action.

Inductive multi_step1 : imp1 -> imp1 -> trace -> Prop :=
| step1_end : forall l, multi_step1 l l []
| step1_step : forall i1 i2 i3 a1 a2,
    step1 i1 i2 a1 -> multi_step1 i2 i3 a2 -> multi_step1 i1 i3 (a1 :: a2).

Inductive multi_step2 : imp2 -> imp2 -> trace -> Prop :=
| step2_end : forall l, multi_step2 l l []
| step2_step : forall i1 i2 i3 a1 a2,
    step2 i1 i2 a1 -> multi_step2 i2 i3 a2 -> multi_step2 i1 i3 (a1 :: a2).

Definition compile (i : imp1) : imp2 :=
  match i with
  | Skip1 => Skip2
  end.

Theorem equiv :
  forall t i1 i2 j1 j2,
    multi_step1 i1 i2 t -> compile i1 = j1 -> multi_step2 j1 j2 t.
Proof.
  intros t i1 i2 j1 j2 Hstep1 Hcomp. inversion Hstep1; subst.
  - destruct i2. simpl.
Admitted.

(*|
Answer
******

The result you are trying to prove is a typical example of a
*simulation* between two transition systems. This case is simple
enough that you can prove it directly; the missing piece in your
attempt is that you need to do induction over the proof of execution:
|*)

Reset equiv. (* .none *)
Theorem equiv :
  forall t i1 i2 j1 j2,
    multi_step1 i1 i2 t -> compile i1 = j1 -> multi_step2 j1 j2 t.
Proof.
  intros t i1 i2 j1 j2 Hstep1 Hcomp.
  induction Hstep1 as [i1|i1 i2 i3 a1 t1 Hstep1 _ IH].
  - destruct i1 as []. simpl in Hcomp. subst j1.
    destruct j2. constructor.
  - destruct Hstep1. specialize (IH Hcomp).
    destruct j1, j2. econstructor; eauto.
    constructor.
Qed.

(*|
However, complex systems require more care. The general recipe looks
as follows:
|*)

Reset Initial. (* .none *)
Variables X Y : Type. (* States of two transition systems *)
Variable A : Type. (* Actions *)

(* Transitions *)
Variable step1 : X -> X -> list A -> Prop.
Variable step2 : Y -> Y -> list A -> Prop.

(* Compilation function *)
Variable compile : X -> Y.

(* Simulation relation; see below *)
Variable R : X -> Y -> Prop.

Theorem forward_simulation :
  forall x1 y1 x2 t,
    R x1 y1 -> step1 x1 x2 t -> exists y2, step2 y1 y2 t /\ R x2 y2.
  (* ... *)
Admitted. (* .none *)

Theorem compilation_is_related :
  forall x, R x (compile x).
  (* ... *)
Admitted. (* .none *)

(*|
This differs from your example in two main ways. First, notice that
the result of the target execution is *existentially* quantified in
the conclusion -- it does not usually make sense to require ``y1`` to
step to *any* ``y2`` whatsoever.

Second, I have added a hypothesis saying that the starting states of
the two transition systems are related by some simulation relation
``R``. This relation should intuitively express when a state ``y`` of
the target system correctly represents a state ``x`` of the source
system, in the sense that it can simulate its behavior.

Finding such a relation requires creativity. Sometimes, it is as
simple as saying that the target is the result of compiling the
source, as you did in your example. More often than not, however, you
need to generalize the relationship between the source and the target
to be able to relate arbitrary executions: the state that you get in
the target during execution might not be the result of compiling a
source state. Once you prove ``forward_simulation`` and
``compilation_is_related``, it should be easy to prove an analogue of
your correctness statement by induction on the multi-step execution
relation.

There are many variations on this basic pattern. For instance,
sometimes a step in the source is not simulated by a single step in
the target, but by multiple ones. Or you might need multiple steps in
the source before you can relate them to a single matching step at the
target.

To conclude, if you are proving the correctness of a compiler, you
might want to consider the opposite statement from the one you
mentioned; namely, that every behavior that you observe in the
compiled program can be explained by a matching source execution --
you certainly would not want the compiled program to exhibit some
behavior that is not allowed by the source language!

.. code-block:: coq

    Theorem compile_is_correct :
      forall x1 y1 y2 t,
        compile x1 = y1 -> multi_step2 y1 y2 t ->
        exists x2, multi_step1 x1 x2 t.
|*)
