(*|
###################################################
Non-positive occurrence due to polymorphic function
###################################################

:Link: https://stackoverflow.com/q/50222311
|*)

(*|
Question
********

I am trying to define a data type with a constructor that takes a
list, and include propositions about this list.

This works fine:
|*)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive Foo :=  MkFoo : list Foo -> Foo.
Reset Foo. (* .none *)

(*| And so does this: |*)

Inductive Foo :=  MkFoo : forall (l : list Foo), Foo.
Reset Foo. (* .none *)

(*| But this fails |*)

Fail Inductive Foo := MkFoo : forall (l : list Foo), l <> [] -> Foo. (* .fails .unfold *)

(*|
I assume that this is because ``[]`` is actually ``@nil Foo`` and Coq
does not like this occurrence of ``Foo``.

I am currently working my way around it using vector, like so
|*)

Require Import Coq.Vectors.Vector.

Inductive Foo := MkFoo : forall n (l : Vector.t Foo n), n <> 0 -> Foo.

(*|
but the complications that arise due to the use of dependent data
structures in Coq make me wonder:

Is there a way I can use plain lists in ``MkFoo`` and still include
propositions about that list?
|*)

(*|
Answer
******

I think there isn't a way of including that constraint directly in the
definition, unfortunately. I see two paths forward:

1. Change the definition of ``mkFoo`` so that it takes the head of the
   list as an additional argument:

   .. code-block:: coq

       mkFoo : Foo -> list Foo -> Foo

2. Define ``Foo`` without any restrictions, and define a separate
   well-formedness predicate:
|*)

Reset Initial. (* .none *)
Require Import Coq.Lists.List.

Inductive Foo := mkFoo : list Foo -> Foo.

Definition isEmpty {T : Type} (x : list T) :=
  match x with
  | nil => true
  | _   => false
  end.

Fixpoint wfFoo (x : Foo) : bool :=
  match x with
  | mkFoo xs => negb (isEmpty xs) && forallb wfFoo xs
  end.

(*|
   You can then show that all the functions on ``Foo`` that you care
   about respect ``wfFoo``. It is also possible to use subset types to
   pack members of ``Foo`` with proofs of ``wfFoo``, guaranteeing that
   clients of ``Foo`` never have to touch ill-formed elements. Since
   ``wfFoo`` is defined as a boolean property, the equation ``wfFoo x
   = true`` is proof-irrelevant, which guarantees that the type ``{ x
   : Foo | wfFoo x = true }`` is well-behaved. The `Mathematical
   Components library <https://github.com/math-comp/math-comp>`__
   provides good support for this kind of construction.
|*)
