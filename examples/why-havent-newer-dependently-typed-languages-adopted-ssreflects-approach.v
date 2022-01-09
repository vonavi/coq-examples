(*|
###########################################################################
Why haven't newer dependently typed languages adopted SSReflect's approach?
###########################################################################

:Link: https://stackoverflow.com/q/49477427
|*)

(*|
Question
********

There are two conventions I've found in Coq's SSReflect extension that
seem particularly useful but which I haven't seen widely adopted in
newer dependently-typed languages (Lean, Agda, Idris).

Firstly, where possible predicates are expressed as boolean-returning
functions rather than inductively defined datatypes. This brings
decidability by default, opens up more opportunities for proof by
computation, and improves checking performance by avoiding the need
for the proof engine to carry around large proof terms. The main
disadvantage I see is the need to use reflection lemmas to manipulate
these boolean predicates when proving.

Secondly, datatypes with invariants are defined as dependent records
containing a simple datatype plus a proof of the invariant. For
instance, fixed length sequences are defined in SSReflect like:
|*)

From mathcomp Require Import tuple. (* .none *)
Print tuple_of. (* .unfold .messages *)

(*|
A ``seq`` and a proof of that sequence's length being a certain value.
This is opposed to how e.g. Idris defines this type:

.. code-block:: idris

    data Vect : (len : Nat) -> (elem : Type) -> Type

A dependently typed datastructure in which the invariant is part of
its type. One advantage of SSReflect's approach is that it allows
reuse, so that for instance many of the functions defined for ``seq``
and proofs about them can still be used with ``tuple`` (by operating
on the underlying ``seq``), whereas with Idris' approach functions
like ``reverse``, ``append`` and the like need to be rewritten for
``Vect``. Lean actually has a SSReflect style equivalent in its
standard library, ``vector``, but it also has an Idris-style ``array``
which seems to have an optimised implementation in the runtime.

One `SSReflect-oriented book <http://ilyasergey.net/pnp/pnp.pdf>`__
even claims the ``Vect n A`` style approach is an antipattern:

    A common anti-pattern in dependently-typed languages and Coq in
    particular is to encode such algebraic properties into the
    definitions of the datatypes and functions themselves (a canonical
    example of such approach are length-indexed lists). While this
    approach looks appealing, as it demonstrates the power of
    dependent types to capture certain properties of datatypes and
    functions on them, it is inherently non-scalable, as there will be
    always another property of interest, which has not been foreseen
    by a designer of the datatype/function, so it will have to be
    encoded as an external fact anyway. This is why we advocate the
    approach, in which datatypes and functions are defined as close to
    the way they would be defined by a programmer as possible, and all
    necessary properties of them are proved separately.

My question is hence, why haven't these approaches been more widely
adopted. Are there disadvantages I'm missing, or maybe their
advantages are less significant in languages with better support for
dependent pattern matching than Coq?
|*)

(*|
Answer (Daniel Schepler)
************************

I can provide some thoughts on the first point (defining predicates as
boolean-returning functions). My biggest issue with this approach is:
then it is by definition impossible for the function to have bugs,
even if it turns out what it's calculating isn't what you intended it
to calculate. In many cases, it would also obscure what you actually
mean by the predicate if you have to include implementation details of
the decision procedure for the predicate in its definition.

In mathematical applications, there will also be issues if you want to
define a predicate which is a specialization of something which is not
decidable in general, even if it happens to be decidable in your
specific case. One example of what I'm talking about here would be
defining the group with a given presentation: in Coq, a common way to
define this would be the setoid with underlying set being formal
expressions in the generators, and the equality given by "word
equivalence". In general, this relation is not decidable, though in
many specific cases it is. However, if you are restricted to defining
groups with presentations where the word problem is decidable, then
you lose the ability to define the unifying concept which ties all the
different examples together, and prove things generically about finite
presentations or about finitely presented groups. On the other hand,
defining the word equivalence relation as an abstract ``Prop`` or
equivalent is straightforward (if possibly a little long).

Personally, I prefer to give the most transparent possible definition
of the predicate first, and then provide decision procedures where
possible (functions returning values of type ``{P} + {~P}`` is my
preference here, though the boolean-returning functions would work
well too). Coq's typeclass mechanism could provide a convenient way to
register such decision procedures; for example:
|*)

Class Decision (P : Prop) : Set :=
  decide : {P} + {~P}.
Arguments decide P {Decision}.

Instance True_dec : Decision True := left _ I.

Instance and_dec (P Q : Prop) `{DP : Decision P} `{DQ : Decision Q} :
  Decision (P /\ Q) :=
  match DP, DQ with
  | left p, left q => left _ (conj p q)
  | _, right not_q => right _ (fun H : P /\ Q =>
                                 match H with
                                 | conj _ q => False_ind False (not_q q)
                                 end)
  | right not_p, _ => right _ (fun H : P /\ Q =>
                                 match H with
                                 | conj p _ => False_ind False (not_p p)
                                 end)
  end.

(* Recap standard library definition of Forall *)
Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
| Forall_nil : Forall P nil
| Forall_cons : forall h t, P h -> Forall P t -> Forall P (cons h t).
(* Or, if you prefer:
   Fixpoint Forall {A : Type} (P : A -> Prop) (l : list A) : Prop :=
   match l with
   | nil => True
   | cons h t => P h /\ Forall P t
   end.
 *)

Program Fixpoint Forall_dec {A : Type} (P : A->Prop)
        `{forall x : A, Decision (P x)} (l : list A) :
  Decision (Forall P l) :=
  match l with
  | nil => left _ _
  | cons h t => if decide (P h) then
                  if Forall_dec P t then
                    left _ _
                  else
                    right _ _
                else
                  right _ _
  end.
(* resolve obligations here *)
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Existing Instance Forall_dec.

(*|
Answer (user3237465)
********************

    This brings decidability by default, opens up more opportunities
    for proof by computation, and improves checking performance by
    avoiding the need for the proof engine to carry around large proof
    terms.

You don't have to carry around large terms as described in the `Edwin
Brady's thesis
<https://eb.host.cs.st-andrews.ac.uk/writings/thesis.pdf>`__ under the
name of "forcing optimisation". Agda does have forcing which affects
type checking (especially how universes are computed is relevant), but
I'm not sure if stuff used only at the type check time really gets
erased before the run time. Anyway, Agda has two notions of
irrelevance: ``.(eq : p ≡ q)`` is the usual irrelevance (meaning
``eq`` is irrelevant at the type checking time, so it's definitionally
equal to any other term of such type) and ``..(x : A)`` is spine
irrelevance (not sure if it's a correct term. I think Agda sources
call such thing "non-strict irrelevance") which is literally for
erasion of computationally irrelevant, but not completely irrelevant
terms. So you can define

.. code-block:: agda

    data Vec {α} (A : Set α) : ..(n : ℕ) -> Set α where
      [] : Vec A 0
      _∷_ : ∀ ..{n} -> A -> Vec A n -> Vec A (suc n)

and ``n`` will be erased before the run time. Or at least it seems to
be designed so, it's hard to be sure, because Agda has lots of poorly
documented features.

And you can write those zero-cost proofs in Coq, just because it too
implements irrelevance for stuff that lives in ``Prop``. But
irrelevance is built-in into Coq's theory very deeply, while in Agda
it's a separate feature, so it's perfectly understandable, why people
find use of irrelevance in Coq more readily than in Agda.

    One advantage of SSReflect's approach is that it allows reuse, so
    that for instance many of the functions defined for ``seq`` and
    proofs about them can still be used with ``tuple`` (by operating
    on the underlying ``seq``), whereas with Idris' approach functions
    like reverse, append and the like need to be rewritten for
    ``Vect``.

It's not a real reuse if you have to prove properties anyway and those
proofs have the same complexity as functions defined over indexed
data. It's also inconvenient to do the job of a unification machinery
and pass around explicit proofs and apply lemmas to get ``length xs ≡
n`` from ``suc (length xs) ≡ n`` (and also ``sym``, ``trans``,
``subst`` and all other lemmas that a unification machinery can save
you from in many cases). Moreover, you lose some clarity by abusing
propositional equality: having ``xs : List A; length xs ≡ n + m``
instead of ``xs : Vec A (n + m)`` doesn't improve readability of your
contexts, especially if they are huge which is often the case. And
there is another problem: sometimes it's just harder to define a
function using SSReflect's approach: you mentioned ``reverse`` for
``Vect``, I challenge you to define this function from scratch (with
``reverse`` for ``List`` as a "reused" part under the hood) and then
compare your solution to the definition in ``Data.Vec`` from the Agda
standard library. And if you don't have irrelevance enabled for
propositions by default (which is the case for Agda), then you'd also
need to prove properties about proofs if you want to prove, say,
``reverse (reverse xs) ≡ xs`` which is a lot of non-trivial
boilerplate.

So SSReflect's approach is not perfect. The other one is too. Is there
anything that improves upon both? Yes, Ornaments (see `Ornamental
Algebras, Algebraic Ornaments
<http://plv.mpi-sws.org/plerg/papers/mcbride-ornaments-2up.pdf>`__ and
`The essence of ornaments
<https://pages.lip6.fr/Pierre-Evariste.Dagand/stuffs/journal-2013-catorn-jfp/paper.pdf>`__).
You can easily get ``Vec`` from ``List`` by applying the corresponding
ornamental algebra, but I can't say how much code reuse you'll get
from it and whether types will drive you nuts or not. I heard people
actually use ornaments somewhere.

So it's not that we have an ideal SSReflect's solution and others
refuse to adopt it. There is just a hope for a more suitable way to
get actual code reuse.

UPDATE
======

**Anton Trunov** in their comment made me realize I'm a bit too
Agda-minded and people in Coq have tactics which can simplify proofs a
lot, so proving in Coq is generally easier (provided you have weapons
like ``crush`` from the `CPDT <http://adam.chlipala.net/cpdt/>`__
book) than defining functions over data. Well, then I guess proof
irrelevance by default and heavy tactics machinery is what makes
SSReflect's approach effective in Coq.

----

**A (Anton Trunov):** Defining ``reverse`` function is easy:
|*)

Reset Initial. (* .none *)
From Coq Require Import ssreflect ssrfun ssrbool. (* .none *)
From mathcomp Require Import eqtype seq tuple. (* .none *)
Definition trev T n (t : n.-tuple T) := [tuple of rev t].

(*|
Here we have reused ``rev`` function for lists (called ``seq`` in
ssr-speak). Proving that ``trev`` is involutive is easy as well:
|*)

Lemma trevK T n : involutive (@trev T n).
Proof. by move=>t; apply: val_inj; rewrite /= revK. Qed.

(*|
Here we again reuse ``revK`` for lists and the non-trivial part
proof-irrelevance lemma ``val_inj``.

**Q:** @AntonTrunov, interesting, thank you. Could you please
elaborate how the proof works under the hood?

**Q:** @AntonTrunov, oh, no, I mean a real reverse which appears to be
named ``rev'`` in the Coq sources. Not the silly ``| x :: l' => rev l'
++ [x]``.

**A (Anton Trunov):** I have used mathcomp's `linear time rev
<https://github.com/math-comp/math-comp/blob/c17414bbef21bb3d0b96ee004c29ef7d56e55e2e/mathcomp/ssreflect/seq.v#L781>`__.

**A (Anton Trunov):** The proof I provided above relies on ``val_inj``
lemma to strip off the ``_ : size tval == n`` part. In SSReflect
``==`` means boolean decidable equality and we operate on ``nat``, so
``val_inj`` removes the proof-irrelevant part of ``Tuple`` and lets us
deal with the underlying lists so we can reuse the list lemmas. Here
is a `gist
<https://gist.github.com/anton-trunov/1c82bdb3b77a3488b1cd909328631e05>`__
with all the imports.
|*)
