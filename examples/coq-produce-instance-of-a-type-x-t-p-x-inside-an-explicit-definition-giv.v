(*|
###########################################################################################################
Coq produce instance of a type ``{x : T | P x}`` inside an explicit definition given an ``x`` of type ``T``
###########################################################################################################

:Link: https://proofassistants.stackexchange.com/q/885
|*)

(*|
Question
********

I'm trying to formalize a simple type system in Coq as an exercise.

I have a type ``Item`` and a type ``{x : Item | IsNormal Item}``. If
``Sort`` is a constructor of ``Item`` and ``Sort`` satisfies
``IsNormal``, what's the most natural way to produce an instance of
``{x : Item | IsNormal Item}`` where the ``Item`` in question is
``Sort``?

----

I have an inductive type called ``Item`` which might be a read of a
free variable (in this case a free variable is an ``N``).

I want to introduce a distinction between terms that are headed by a
variable read and terms that are definitely not headed by a variable.

I'm trying to use ``sig types`` for this (see `this answer
<https://proofassistants.stackexchange.com/a/731>`__ and `this link
<https://coq.inria.fr/library/Coq.Init.Specif.html>`__).

The thing I am having problems with is this definition. (I also tried
a shorter version with ``match x with | Read x' => env x' | _ => x
end`` as the body)

.. coq:: none
|*)

Inductive Item : Type :=
| Sort : Item
| N : Item
| T : Item
| Nat : nat -> Item
| Read : nat -> Item.

Definition IsNormal (a : Item) : Prop :=
  match a with
  | Read _ => False
  | _ => True
  end.

Definition NormalItem : Type := { x : Item | IsNormal x }.

(*||*)

Fail Definition in_env (env : nat -> NormalItem) (x : Item) : NormalItem :=
  match x with
  | Read x' => env x'
  | Sort => Sort
  | N => N
  | T => T
  | Nat n => Nat n
  end. (* .fails *)

(*|
``NormalItem`` is defined as ``{ x : Item | IsNormal x }``, where
``IsNormal`` picks out the members of ``Item`` that are not headed by
``Read``.

This definition doesn't type check (error shown below).
|*)

Fail Definition in_env (env : nat -> NormalItem) (x : Item) : NormalItem :=
  match x with
  | Read x' => env x'
  | Sort => Sort
  | N => N
  | T => T
  | Nat n => Nat n
  end. (* .unfold .messages *)

(*|
I think this is because ``Sort`` needs to instead be a pair consisting
of an ``Item`` and a proof that the item in question satisfies
``isNormal``. I cannot figure out, however, how to write such a thing.

Appendix A
==========
|*)

Reset Initial. (* .none *)
Require Import Arith.
Require Import List.
Require Import Specif.
Require Import Notations.

Open Scope nat_scope.

Inductive Item : Type :=
| Sort : Item
| N : Item
| T : Item
| Nat : nat -> Item
| Read : nat -> Item.

Definition IsNormal (a : Item) : Prop :=
  match a with
  | Read _ => False
  | _ => True
  end.

Definition NormalItem : Type := { x : Item | IsNormal x }.

(*|
Answer (Meven Lennon-Bertrand)
******************************

If you look at how ``{ x : A | P }`` is defined (for instance using
``Locate "{"``. to find out it's a notation for ``sig`` and ``Print
sig``. to see the definition of ``sig``), you can see that to
construct an inhabitant of ``NormalItem`` you indeed need to provide a
pair (or, rather, two arguments) to the unique constructor ``exists``
of ``sig``.

There are two ways to do this. The first one is to simply alter your
definition to the following (I took the liberty of factoring out the
branches as you suggested)
|*)

Definition in_env (env : nat -> NormalItem) (x : Item) : NormalItem :=
  match x with
  | Read x' => env x'
  | y => exist _ y I
  end.

(*|
here ``I`` is the only constructor of ``True``, to which ``IsNormal
y`` reduces to in those branches.

Now this works on this simple example because the proof you have to
write by hand is very simple, but often you want to do a "mixed"
definition, where you give some part of it in a direct way, but write
down proofs interactively. You can do this by hand, relying on the
``refine`` tactic:
|*)

Definition in_env' (env : nat -> NormalItem) (x : Item) : NormalItem.
Proof.
  refine (
      match x with
      | Read x' => env x'
      | Sort => exist _ Sort _
      | N => exist _ N _
      | T => exist _ T _
      | Nat n => exist _ (Nat n) _
      end).
  all: cbn; auto.
Defined.

(*|
However, doing this by hand can get quite tedious quite fast. Happily,
`Program <https://coq.inria.fr/refman/addendum/program.html>`__ and
`Equations <https://coq.inria.fr/refman/addendum/program.html>`__ can
help making this kind of definitions more natural.
|*)

(*|
Answer (Andrej Bauer)
*********************

It is very unlikely that you really want to organize your
formalization using predicates such as ``IsNormal``. Instead you
should define types that already carry precisely the correct
information and use those.

I am guessing what you are doing, so for a better answer, please
explain in your question what the Grand Plan of your formalization is.
|*)

Reset Initial. (* .none *)
Inductive NormalItem :=
| Sort : NormalItem
| N : NormalItem
| T : NormalItem
| Nat : nat -> NormalItem.

Inductive Item : Type :=
| Normal : NormalItem -> Item
| Read : nat -> Item.

Definition in_env (env : nat -> NormalItem) (x : Item) : NormalItem :=
  match x with
  | Read x' => env x'
  | Normal y => y
  end.
