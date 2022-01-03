(*|
####################
Dependent Pair Types
####################

:Link: https://stackoverflow.com/q/51053375
|*)

(*|
Question
********

In software foundations, `Logic in Coq
<http://www.seas.upenn.edu/~cis500/current/sf/lf-current/Logic.HTML>`__,
we are introduced to parametrized propositions:
|*)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three. (* .unfold *)

(*|
which reminds me of dependent pair types, which from `Reading HoTT in
Coq <https://mdnahas.github.io/doc/Reading_HoTT_in_Coq.pdf>`__ we have
dependent pair types to be defined:
|*)

Inductive sigT {A : Type} (P : A -> Type) : Type :=
  existT : forall x : A, P x -> sigT P.

(*|
Can someone explain how are they different and also in Reading HoTT in
Coq, it says "Since we haven't defined propositional equality, we
can't do much that is interesting here", why can't we do anything
interesting without propositional equality?
|*)

(*|
Answer
******

Let us pretend for now that the HoTT code uses ``A -> Prop`` instead
of ``A -> Type``; the difference between the two is orthogonal to your
question.

A parametrized proposition ``P : A -> Prop`` is simply property of
elements of the type ``A``. Besides the simple ``is_three``
proposition above, we can express more complex properties of natural
numbers in this fashion. For instance:
|*)

Definition even (n : nat) : Prop :=
  exists p, n = 2 * p.

Definition prime (n : nat) : Prop :=
  n >= 2 /\
  forall p q, n = p * q -> p = n \/ p = 1.

(*|
The type ``sigT A P`` type allows us to restrict the type ``A`` to
elements that satisfy the property ``P``. For instance, ``sigT nat
even`` is the type of all even numbers, ``sigT nat prime`` is the type
of all prime numbers, etc. In Coq, properties are the more primitive
concept, and subset types like ``sigT`` are a derived concept.

In traditional mathematics, the concepts of property and subset can
almost be conflated: saying that 2 is a prime number is equivalent to
saying that it belongs to the set of all prime numbers. In Coq's type
theory, this is not quite the case, because being an element of a type
is not a proposition: you cannot, for instance, state a theorem saying
that 2 is an element of ``sigT nat prime``. The following snippet
throws an error:
|*)

Fail Lemma bogus : (2 : {x : nat & prime x}). (* .fails .unfold *)

(*|
(The ``{ ... & ... }`` is syntactic sugar for the ``sigT`` type
defined in Coq's standard library.)

The closest we can get is to say that 2 can be extracted from that
type:
|*)

Lemma fixed : exists x : {x : nat & prime x}, 2 = projT1 x.
Admitted. (* .none *)

(*|
where ``projT1`` is the function that extracts the first component of
the dependent pair. However, this is much more cumbersome than simply
stating that 2 is prime:
|*)

Lemma prime_two : prime 2.
Admitted. (* .none *)

(*|
In general, parametrized propositions are more useful in Coq, but
there are cases where ``sigT`` type comes in handy; for instance, when
we only care about the elements of a type that satisfy a certain
property. Imagine that you implement a associative map in Coq using a
type of binary search trees. You might begin by defining a type
``tree`` of *arbitrary* trees:
|*)

Inductive tree :=
| Leaf : tree
| Node : tree -> nat -> nat -> tree -> tree.

(*|
This type defines a binary tree whose nodes store a key-value pair of
natural numbers. To implement functions for looking up an element,
updating a value, etc., using this type, we might maintain the
invariant that the keys of the tree are sorted (that is, that the keys
on the left subtree are less than the keys of a node, and the opposite
for the right subtree). Since users of this tree will not want to
consider trees that do not satisfy this invariant, we might use
instead the type ``sigT tree well_formed``, where ``well_formed : tree
-> Prop`` expresses the above invariant. The main advantage is that
this simplifies the interface of our library: instead of having a
separate lemma saying that the insertion function preserves the
invariant, this would be automatically expressed in the type of the
insertion function itself; users wouldn't even need to bother arguing
that the trees that they construct using the interface respect the
invariant.

As for your second question, equality is so fundamental that it is
hard to define interesting properties without it. For instance, the
properties ``even`` and ``prime`` above are both defined using
equality.
|*)
