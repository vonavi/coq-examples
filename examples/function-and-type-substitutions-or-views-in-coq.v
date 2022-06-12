(*|
################################################
Function- and Type substitutions or Views in Coq
################################################

:Link: https://stackoverflow.com/q/29870487
|*)

(*|
Question
********

I proved some theorems about lists, and extracted algorithms from
them. Now I want to use heaps instead, because lookup and
concatenation are faster. What I currently do to achieve this is to
just use custom definitions for the extracted list type. I would like
to do this in a more formal way, but ideally without having to redo
all of my proofs. Lets say I have a type

.. code-block:: coq

    Heap : Set -> Set

and an isomorphism

.. code-block:: coq

    f : forall A, Heap A -> List A.

Furthermore, I have functions ``H_app`` and ``H_nth``, such that

.. code-block:: coq

    H_app (f a) (f b) = f (a ++ b)

and

.. code-block:: coq

    H_nth (f a) = nth a

On the one hand, I would have to replace every list-recursion by a
specialized function that mimics list recursion. On the other hand,
beforehand I would want to replace ``++`` and ``nth`` by ``H_app`` and
``H_nth``, so the extracted algorithms would be faster. The problem is
that I use tactics like ``simpl`` and ``compute`` in some places,
which will probably fail if I just replace everything in the proof
code. It would be good to have a possibility to "overload" the
functions afterwards.

Is something like this possible?

Edit: To clarify, a similar problem arises with numbers: I have some
old proofs that use ``nat``, but the numbers are getting too large.
Using ``BinNat`` would be better, but is it possible to use ``BinNat``
instead of ``nat`` also in the old proofs without too much
modification? (And especially, replace inefficient usages of ``+`` by
the more efficient definition for ``BinNat``?)
|*)

(*|
Answer
******

Just for the sake of clarity, I take it that ``Heap`` must look like
this:

.. coq:: none
|*)

Set Implicit Arguments.

Require Import List.
Import ListNotations.

(*||*)

Inductive Heap A : Type :=
| Node : Heap A -> A -> Heap A -> Heap A
| Leaf : Heap A.

(*| with ``f`` being defined as |*)

Fixpoint f A (h : Heap A) : list A :=
  match h with
  | Node h1 a h2 => f h1 ++ a :: f h2
  | Leaf _ => []
  end.

(*|
If this is the case, then ``f`` does *not* define an isomorphism
between ``Heap A`` and ``list A`` for all ``A``. Instead, we can find
a function ``g : forall A, list A -> Heap A`` such that

.. code-block:: coq

    forall A (l : list A), f (g l) = l

Nevertheless, we would like to say that both ``Heap`` and ``list`` are
equivalent in some sense when they are used to implement the same
abstraction, namely sets of elements of some type.

There is a precise and formal way in which we can validate this idea
in languages that have `parametric polymorphism
<http://en.wikipedia.org/wiki/Parametric_polymorphism>`__, such as
Coq. This principle, known as `parametricity
<http://en.wikipedia.org/wiki/Parametricity>`__, roughly says that
parametrically polymorphic functions respect relations that we impose
on types we instantiate them with.

This is a little bit abstract, so let's try to make it more concrete.
Suppose that you have a function over lists (say, ``foo``) that uses
only ``++`` and ``nth``. To be able to replace ``foo`` by an
equivalent version on ``Heap`` using parametricity, we need to make
``foo``'s definition polymorphic, abstracting over the functions over
lists:
|*)

Definition foo (T : Set -> Set)
           (app : forall A, T A -> T A -> T A)
           (nth : forall A, T A -> nat -> option A)
           A (l : T A) : T A.
  (* ... *)
Admitted. (* .none *)

(*|
You would first prove properties of foo by instantiating it over lists:

.. code-block:: coq

    Definition list_foo := foo list app nth_error.

    Lemma list_foo_lemma : (* Some statement *).

Now, because we now that ``H_app`` and ``H_nth`` are compatible with
their list counterparts, and because ``foo`` is polymorphic, the
theory of parametricity says that we can prove

.. code-block:: coq

    Definition H_foo := foo Heap H_app H_nth.

    Lemma foo_param : forall A (h : Heap A),
        f (H_foo h) = list_foo (f h).

with this lemma in hand, it should be possible to transport properties
of ``list_foo`` to similar properties of ``H_foo``. For instance, as a
trivial example, we can show that ``H_app`` is associative, up to
conversion to a list:

.. code-block:: coq

    forall A (h1 h2 h3 : Heap A),
      list_foo (H_app h1 (H_app h2 h3)) =
        list_foo (H_app (H_app h1 h2) h3).

What's nice about parametricity is that it applies to *any*
parametrically polymorphic function: as long as appropriate
compatibility conditions hold of your types, it should be possible to
relate two instantiations of a given function in a similar fashion to
``foo_param``.

There are two problems, however. The first one is having to change
your base definitions to polymorphic ones, which is probably not so
bad. What's worse, though, is that even though parametricity ensures
that it is always possible to prove lemmas such as ``foo_param`` under
certain conditions, Coq does not give you that for free, and you still
need to show these lemmas by hand. There are two things that could
help alleviate your pain:

1. There's a `parametricity plugin
   <https://github.com/mlasson/paramcoq>`__ for Coq (CoqParam) which
   should help deriving the boilerplate proofs for you automatically.
   I have never used it, though, so I can't really say how easy it is
   to use.

2. The Coq Effective Algebra Library (or `CoqEAL
   <https://github.com/CoqEAL/CoqEAL>`__, for short) uses
   parametricity to prove things about efficient algorithms while
   reasoning over more convenient ones. In particular, they define
   refinements that allow one to switch between ``nat`` and
   ``BinNat``, as you suggested. Internally, they use an
   infrastructure based on type-class inference, which you could adapt
   to your original example, but I heard that they are currently
   migrating their implementation to use CoqParam instead.
|*)
