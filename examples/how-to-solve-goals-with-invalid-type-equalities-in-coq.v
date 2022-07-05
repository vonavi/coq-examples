(*|
#######################################################
How to solve goals with invalid type equalities in Coq?
#######################################################

:Link: https://stackoverflow.com/q/12224318
|*)

(*|
Question
********

My proof scripts are giving me stupid type equalities like ``nat =
bool`` or ``nat = list unit`` which I need to use to solve
contradictory goals.

In normal math, this would be trivial. Given sets ``bool := { true,
false }`` and ``nat := { 0, 1, 2, ... }`` I know that ``true ∈ bool``,
but ``true ∉ nat``, hence ``bool ≠ nat``. In Coq, I don't even know
how to state that ``true :̸ nat``.

Question
========

Is there a way to show that these equalities are false? Or maybe, is
it impossible?
|*)

(*|
Answer (pigworker)
******************

**tl;dr** Cardinality arguments are the only way to show types
unequal. You can certainly automate cardinality arguments more
effectively with a bit of reflection. If you want to go further, give
your types a syntactic representation by constructing a universe,
ensuring your proof obligations are framed as syntactic inequality of
representations rather than semantic inequality of types.

Isomorphism as Equality
=======================

It's widely believed (and there may even be a proof of it somewhere)
that Coq's logic is consistent with the axiom that *isomorphic* sets
are *propositionally equal*. Indeed, this is a consequence of the
Univalence Axiom from Vladimir Voevodsky, which people are having so
much fun with at the moment. I must say, it seems very plausible that
it is consistent (in the absence of typecase), and that a
computational interpretation can be constructed which somehow
transports values between equal types by inserting whichever component
of the isomorphism is needed at any given moment.

If we assume that such an axiom is consistent, we discover that type
inequality in the logic as it stands can hold by only refuting the
existence of type isomorphism. As a result, your partial solution is,
at least in principle, where it's at. Enumerability is rather key to
showing non-isomorphism. I'm not sure what the status of ``nat = (nat
-> nat)`` might be, but it is clear *from outside the system* that
every inhabitant of ``nat -> nat`` has a normal form, and that there
are countably many normal forms: it's at least plausible that there
are consistent axioms or reflection principles which make the logic
more *intensional* and which validate that hypothesis.

Automating Cardinality Arguments
================================

I can see two steps you might take to improve on the present
situation. The less radical step is to improve your generic technology
for making these cardinality arguments by better use of reflection.
You're ideally placed to do so, because in general, you're looking to
show that a finite set is distinct from some larger set. Suppose we
have some notion of ``DList A``, a list of distinct elements of ``A``.
If you can construct an *exhaustive* ``DList A`` and a *longer*
``DList B``, then you can disprove ``A = B``.

There's a lovely definition of ``DList`` by *induction-recursion*, but
Coq doesn't have induction-recursion. Fortunately, it's one of those
definitions we can simulate by careful use of indexing. Forgive my
informal syntax, but let's have

.. code::

    Parameters
      A   : Set
      d   : A -> A -> bool
      dok : forall x y, d x y = true -> x = y -> False

That's ``d`` for "distinct". If a set already has decidable equality,
you can equip it with ``d`` very easily. A large set can be equipped
with an adequate ``d`` for our purposes with not much work. And
actually, that's the crucial step: following the wisdom of the
SSReflect team, we take advantage of the smallness of our domain by
working with ``bool`` rather than ``Prop``, and make the computer do
the heavy lifting.

Now, let us have

.. code::

    DListBody : (A -> bool) -> Set

where the index is the *freshness test* for the list

.. code::

    dnil  : DListBody (const true) (* any element is fresh for the empty list *)
    dsnoc : forall f, (xs : DListBody f) -> (x : A) -> is_true (f x) ->
              DListBody (fun y => f y /\ d x y)

And if you like, you can define ``DList`` wrapping ``DListBody``
existentially. Perhaps that's actually hiding information we want,
though, because to show such a thing exhaustive goes like this:

.. code::

    Exhaustive (f : A -> bool) (mylist : DListBody f) = forall x : A, is_false (f x)

So if you can write down a ``DListBody`` for a finite enumeration, you
can prove it exhaustive just by a case analysis with trivial subgoals.

You then need only make the pigeonholing argument once. When you want
to disprove an equality between types (assuming you already have
suitable candidates for ``d``), you exhaustively enumerate the smaller
and exhibit a longer list from the larger, and that's it.

Working in a Universe
=====================

The more radical alternative is to question why you are getting these
goals in the first place, and whether they really mean what you want
them to. What are types supposed to be, really? There are multiple
possible answers to that question, but it is at least open that they
are in some sense "cardinalities". If you want to think of types as
being more concrete and syntactic, distinct if they are built by
distinct constructions, then you may need to equip types with a more
concrete representation by working in a universe. You define an
inductive datatype of "names" for types, together with the means to
decode names as types, then you reframe your development in terms of
names. You should find that inequality of names follows by ordinary
constructor discrimination.

The snag is that universe constructions can be a bit tricky in Coq,
again because induction-recursion is unsupported. It depends heavily
on what types you need to consider. Maybe you can define inductively
some ``U : Set`` then implement a recursive decoder ``T : U -> Set``.
That's certainly plausible for universes of simple types. If you want
a universe of dependent types, things get a bit sweatier. You can at
least do this much

.. code::

    U : Type   (* note that we've gone up a size *)
    NAT : U
    PI : forall (A : Set), (A -> U) -> U

    T : U -> Set
    T NAT = nat
    T (PI A B) = forall (a : A), T (B a)

but note that the domain of ``PI`` is unencoded in ``Set``, not in
``U``. The inductive-recursive Agdans can get over this, defining
``U`` and ``T`` simultaneously

.. code::

    U : Set   (* nice and small *)
    NAT : U
    PI : forall (A : U), (T A -> U) -> U   (* note the use of T *)

    T : U -> Set
    T NAT = nat
    T (PI A B) = forall (a : T A), T (B a)

but Coq won't have that. Again, the workaround is to use indexing.
Here the cost is that ``U`` is inevitably large.

.. code::

    U : Set -> Type
    NAT : U nat
    PI : forall (A : Set) (B : A -> Set),
           U A -> (forall a, U (B a)) -> U (forall a, B a)

But you can still get a lot of stuff done with a universe built that
way. For example, one can equip such a universe with a computationally
effective `extensional equality
<https://personal.cis.strath.ac.uk/conor.mcbride/pub/JOTT/coq/ott.v>`__.
|*)

(*|
Answer (nobody)
***************

expanded *partial* solution
===========================

For reference, here is my proof for ``nat = bool -> False``. (It's
quite long but I hope it's easy to see the general structure of this
proof.)
|*)

Goal nat = bool -> False.
(* For any two types, if they are actually identical, the identity is an
   isomorphism. *)
Proof.
  assert (forall T U : Set,
             T = U -> exists (f : T -> U) (g : U -> T),
               (forall t, g (f t) = t) /\ (forall u, f (g u) = u))
    as Hiso
      by (intros T U H; rewrite H; exists (@id U); exists (@id U);
          split; intro; reflexivity).
  (* our nat = bool *)
  intro HC.
  (* combining the facts gives an iso between nat and bool *)
  pose proof (Hiso nat bool HC); clear HC Hiso.
  inversion H as [phi [phi_inv [Hl Hr]]]; clear H Hr.
  (* this breaks because ||bool|| = 2 while ||nat|| > 2 -- we get collisions *)
  assert (forall m n o, phi m = phi n \/ phi n = phi o \/ phi m = phi o)
    by (intros m n o;
        case (phi m); case (phi n); case (phi o); clear; tauto).
  (* building the collision for 0, 1 and 2 *)
  pose proof (H 0 1 2) as HC; clear H.
  (* (false) identity preservation for 0, 1, 2 *)
  pose proof (Hl 0) as H0; pose proof (Hl 1) as H1;
    pose proof (Hl 2) as H2; clear Hl.
  (* case analysis on phi calls yields equalities on non-equal numbers... *)
  destruct (phi 0); destruct (phi 1); destruct (phi 2);
    (* ...rewriting leads to an equality '0 = 2' or '0 = 1' or '1 = 2'... *)
    try (rewrite H2 in H0); try (rewrite H1 in H0); try (rewrite H2 in H1);
  (* ...which can be used to solve by constructor inequality *)
    try inversion H0; inversion H1.
Qed.

(*|
As you can see, this is not really usable for large finite types (even
if automated) -- the terms are too big. Any improvement on this would
be great.
|*)
