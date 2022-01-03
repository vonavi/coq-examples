(*|
##########################################################
When are the constructors of an inductive type exhaustive?
##########################################################

:Link: https://stackoverflow.com/q/52301832
|*)

(*|
Question
********

For a simple inductive type like the natural numbers ``nat``, it is
easy to prove that the two constructors (zero and successor) give all
possible natural numbers,
|*)

Lemma nat_destruct (n : nat) : n = O \/ exists m : nat, n = S m.
Proof.
  destruct n.
  - left. reflexivity.
  - right. exists n. reflexivity.
Qed.

(*|
However I hear it is not so simple for equality proofs. There is only
one equality constructor, ``eq_refl``, but Coq cannot prove that
|*)

Lemma eq_destruct : forall (A : Type) (x : A) (prEq : x = x),
    prEq = eq_refl.
Abort. (* .none *)

(*|
What exactly blocks this proof? Probably a first problem is that
equality is not just a type, but a type family ``eq : forall A : Type,
A -> A -> Prop``. Is there a simpler type family where such a proof is
impossible? With 1 or 2 arguments instead of 3 maybe?
|*)

(*|
Answer
******

I wrote about this issue in a `blog post
<http://poleiro.info/posts/2018-01-26-equality-in-coq.html>`__. In
general, this arises when you define a type family over a type that
does not have decidable equality. For example, consider the following
type:
|*)

Inductive foo : Type -> Type :=
| Foo : foo unit.

(*|
It is not possible to show (I am pretty sure) that every inhabitant of
``foo unit`` is of the form ``Foo``.

This phenomenon is easier to see at the level of proof terms. When you
destruct a term of such a family, you must generalize over the index
of the family. You can only relate this index to a known shape such as
``unit`` if the type has decidable equality.

----

**A (András Kovács):** Interestingly though, univalence implies that
every ``foo unit`` is ``Foo``.

**Q:** @AndrásKovács Is this because ``unit`` is contractible? Would
it fail if I replaced ``unit`` by ``bool``?

**A (András Kovács):** Yes, to both questions.
|*)
