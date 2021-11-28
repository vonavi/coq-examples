(*|
#################################################################
Coq - return value of type which is equal to function return type
#################################################################

:Link: https://stackoverflow.com/questions/55422961/coq-return-value-of-type-which-is-equal-to-function-return-type
|*)

(*|
Question
********

By some theorem we know that type ``A`` equals type ``B``. How can I
tell this to Coq compiler during type checking?

I want to implement a non-empty tree such that each node know its
size:
|*)

Require Import Coq.ZArith.ZArith. (* .none *)
Inductive Struct: positive -> Type :=
| Leaf : Struct 1%positive
| Inner: forall {n m}, Struct n -> Struct m -> Struct (n + m).

(*|
I want to create a function which generates a tree of a given size of
logarithmic depth. E.g. ``7 -> 6 + 1 -> (3 + 3) + 1 -> ((2 + 1) + (2 +
1)) + 1 -> (((1 + 1) + 1) + ((1 + 1) + 1)) + 1``
|*)

Fail Fixpoint nat2struct n : (Struct n) :=
  match n with
  | xH => Leaf
  | xO n => Inner (nat2struct n) (nat2struct n)
  | xI n => Inner Leaf (Inner (nat2struct n) (nat2struct n))
  end. (* .unfold .fails *)

(*|
However, I get the error. How can I fix this? We know that ``(1 + n +
n) = xI n``, but Coq doesn't. If I state this theorem before, it
doesn't change anything:
|*)

Theorem nBy2p1: forall n, Pos.add 1%positive (n + n) = xI n.
Proof. Admitted.
Hint Resolve nBy2p1.

(*|
Are there some hints for Coq to be aware of this theorem?

PS1: is this theorem already proved in standard library? I didn't find
one.

PS2: I actually want to split more naturally: ``7 -> 4 + 3 -> (2 + 2)
+ (2 + 1) -> ((1 + 1) + (1 + 1)) + ((1 + 1) + 1)``. Is it possible? I
don't know how to write it so that Coq understands that the function
converges.
|*)

(*|
Answer
******

When type-checking, Coq uses a weaker form of equality (sometimes
called definitional, judgemental, or computational equality). Unlike
propositional equality (what "=" binds to by default), definitional
equality is decidable. Coq can take any two terms and decide if one is
convertible into the other. If propositional equality were allowed in
type-checking, type-checking would no longer be decidable [1]_.

To fix your problem (and it is a pretty big problem) you have a few
options.

Make ``Struct`` a record
========================

I'll demonstrate the principle using lists. First, we have the notion
of unsized lists.
|*)

Inductive UnsizedList (A: Type) :=
| unil
| ucons (a: A) (u: UnsizedList A).

Arguments unil {A}, A.
Arguments ucons {A} a u, A a u.

Fixpoint length {A: Type} (u: UnsizedList A) :=
match u with
| unil => 0
| ucons _ u' => S (length u')
end.

(*|
We can also define a sized list, where every element of ``SizedList A
n`` has length ``n``.
|*)

Inductive SizedList (A: Type): nat -> Type :=
| snil: SizedList A 0
| scons {n: nat} (a: A) (u: SizedList A n): SizedList A (S n).

(*|
This definition runs into the exact same problem as yours. For
example, if you want to show that concatenation is associative, you
can't simply prove ``concat (concat u v) w = concat u (concat v w)``,
since the two sides of the equality have different types (``(i + j) +
k vs i + (j + k)``). If we could simply tell Coq what size we expect
the list to be, then prove it later, we could solve this. That's what
this definition does, which packs together an ``UnsizedList`` with a
proof that that list has the desired length.
|*)

Record SizedListPr (A: Type) (n: nat): Type :=
  {
  list: UnsizedList A;
  list_len_eq: length list = n;
  }.

(*|
Now we can have ``concat (concat u v) w = concat u (concat v w)``; we
just need to prove that both sides have length ``(i + j) + k``.

Use coercions
=============

This approach can get pretty messy if you aren't careful, so it's not
often the preferred approach.

Let me define a sort of coercion that maps elements of type ``P x`` to
elements of type ``P y`` if ``x = y``\ [2]_.
|*)

Definition coercion {A: Type} (P: A -> Type) {x y: A} (p: x = y): P x -> P y :=
  match p with
  | eq_refl => fun t => t
  end.

(*|
Here we use induction on the term ``p: x = y``. The induction
principle says, essentially, that if we can prove something when ``x``
and ``y`` are definitionally equal, then we can prove it when they're
propositionaly equal [3]_. When ``P x`` and ``P y`` are the same, we
can just use the identity function.

Now, for example, the statement of associativity of concatenation for
sized lists is ``concat (concat u v) w = coercion (SizedList A)
(add_assoc) (concat u (concat v w))``. So we coerce something of type
``SizedList A (i + (j + k))`` to something of type ``SizedList A ((i +
j) + k)`` using the equality ``add_assoc: i + (j + k) = (i + j) + k``
(I've left out some parameters for readability).

----

What choice you make is up to you. A discussion of this problem and
related problems, as well as some additional resolutions can be found
at the *Certified Programming with Dependent Types* page `Equality
<http://adam.chlipala.net/cpdt/html/Equality.html>`_.

----

.. [1] See *extensional type theory* for a class of theories where
       this typically happens. `Martin Hofmann's thesis
       <http://www.lfcs.inf.ed.ac.uk/reports/95/ECS-LFCS-95-327/>`_
       has an overview of the difference between intensional and
       extensional theories.
.. [2] If you're familiar with Homotopy Type Theory, this is
       ``transport``.
.. [3] There are enough caveats on this statement that the differences
       between propositional and definitional equality still exist.
|*)
