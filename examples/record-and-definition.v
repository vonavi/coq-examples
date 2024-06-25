(*|
#############################
``Record`` and ``Definition``
#############################

:Link: https://stackoverflow.com/q/9577000
|*)

(*|
Question
********

I have a question about the: ``Record`` and ``Definition``

I have this definition:

.. coq:: none
|*)
Variable term : Type.
Variable beq_term : term -> term -> bool.
Variable band_term : (term -> bool) -> (term -> bool) -> term -> term -> bool.
Notation "a && b" := (band_term a b).

(*||*)

Definition rule := term -> term.

(*| and I write a boolean function for it. |*)

Definition beq_rule a b := beq_term a && beq_term b.

(*|
where ``beq_term : term -> term -> bool``.

So my definition of ``beq_rule`` actually return exactly type of
``beq_term`` which is not what I want here. I want it return for me a
type: ``rule -> rule -> bool``.

So I changed a definition of rule by ``Record``:
|*)

Reset rule. (* .none *)
Record rule := mkRule {lhs : term; rhs : term}.

(*| and |*)

Definition beq_rule (a b : rule) : bool :=
  beq_term (lhs a) (lhs b) && beq_term (rhs a) (rhs b).

(*|
My question is that:

1) What is the different between my first defined ``rule`` used
   ``Definition`` and another used ``Record``?
2) If I want to define rule by ``Definition`` can I give an alias
   ``lhs`` and ``rhs`` likes in ``Record`` definition?
|*)

(*|
Answer
******

Your two definitions of ``rule`` are saying totally different things
|*)

Reset rule. (* .none *)
Definition rule := term -> term.

(*|
is defining rule as a type (or ``Prop``) alias of the function type
``term -> term``. Hence
|*)

Definition not_what_you_meant : rule := fun t => t.

(*|
will happily compile.

As to the relation between ``Record`` and ``Definition``. ``Record``
is just a macro that converts into an ``Inductive``. So
|*)

Reset rule. (* .none *)
Record rule := mkRule {lhs : term; rhs : term}.

(*| is the same as |*)

Print rule. (* .unfold .messages *)

(*| plus accessor functions |*)

Print lhs. (* .unfold .messages *)

(*|
You should think of ``Inductive`` as being fundamentally different
from ``Definition``. ``Definition`` defines an *alias*. Another way of
saying this is ``Definition``\ s are "referentially transparent", you
can (up to variable renaming) always substitute the right hand side of
a definition for any occurrence of its name.

``Inductive`` on the other hand defines type (elements of Coqs
universes) by listing off a set of constructors. In more logical way
of thinking, ``Inductive`` defines a logical proposition in terms of
its elimination/introduction rules in a way that ensures "harmony".
|*)
