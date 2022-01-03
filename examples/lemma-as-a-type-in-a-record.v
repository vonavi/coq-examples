(*|
###########################
Lemma as a type in a record
###########################

:Link: https://stackoverflow.com/q/55563771
|*)

(*|
Question
********

Beginner here! How do we I interpret a record that looks something
like this?
|*)

Require Import ssrbool. (* .none *)
Fail Record test A B :=
  {
  CA: forall m, A m;
  CB: forall a b m, CA m ==> B(a, b);
  }. (* .fails *)

(*|
I am trying to get a sense of what an instance of this record would
look like and moreover, what it means to have a quantified lemma as a
type.
|*)

(*|
Answer
******

What you are writing cannot make sense because the notation ``_ ==>
_`` is supposed to link two boolean values. But ``CA`` has type ``A
m``, which is itself a type, not a boolean value.

One possibility to go forward would be to make ``CA`` a boolean
function that could represent the ``A`` predicate.

Another difficulty with your hypothetical record is that we don't know
what are the input types for ``A`` and ``B``, so I will assume we live
in an ambient type ``T`` over which quantifications appear. So here is
a variant:
|*)

Record test (T : Type) (A : T -> Prop) (B : T * T -> bool) :=
  {
  CA : T -> bool;
  CA_A : forall m, CA m = true -> A m;
  CB : forall a b m, (CA m ==> B(a, b)) = true
  }.

(*|
This example forces you to understand that there are two distinct
concepts in this logical language: ``bool`` values and ``Prop``
values. They represent different things, which can sometimes be
amalgamated but you need to make the distinction clear in your head to
leave the category of *beginner*.

For your last sentence "what it means to have a quantified lemma as a
type" here is another explanation.

When programming with a conventional programming language, you can
return arrays of integers. However, you cannot be explicit and say
that you want to return an array of integers of a *specific length*.
In Gallina (the basic programming language of Coq), you can define a
type of arrays of length 10. Let us assume that such a type would be
written ``array n``. So ``array 10`` and ``array 11`` would be two
different types. A function that takes as input a number ``n`` and
return as output an array of length ``n`` would have the following
type:

.. code-block:: coq

    forall n, array n

So an object that has a quantified formula as a type simply is a
function.

From a logical point of view, the statement ``forall n, array n`` is
usually read as *for every* ``n`` *there exists an array of* ``size
n``. This statement is probably no surprise to you.

So the type of an array depends on an indice. Now we can think of
another type, for example, the *type of proofs that* ``n`` *is prime*.
Let's assume this type is written ``prime n``. Surely, there are
numbers that are not prime, so for example the type ``prime 4`` should
not contain any proof at all. Now I may write a function called
``test_prime : nat -> bool`` with the property that when it returns
``true`` I have the guarantee that the input is prime. This would be
written as such:

.. code-block:: coq

    forall n, test_prime n = true -> prime n

Now, if I want to define a collection of all correct prime testing
functions, I would want to associate in one piece of data the function
and the proof that it is correct, so I would define the following data
type.
|*)

Parameter prime : nat -> Prop. (* .none *)
Record certified_prime_test :=
  {
  test_prime : nat -> bool;
  certificate : forall n, test_prime n = true -> prime n
  }.

(*|
So records that contain universally quantified formulas can be in one
of these two categories: either one component is one of this function
whose output varies across several types of the same family (like in
the example of ``array``) or one of the components actually brings
more logical information about another component which is a function.
In the ``certified_prime_test`` example, the ``certificate`` component
brings more information about the ``test_prime`` function.
|*)
