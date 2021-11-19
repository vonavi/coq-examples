(*|
Why do Calculus of Construction based languages use Setoids so much?
====================================================================

:Link: https://stackoverflow.com/questions/65493694/why-do-calculus-of-construction-based-languages-use-setoids-so-much
|*)

(*|
Question
--------

One finds that Setoids are widely used in languages such as Agda, Coq,
... Indeed languages such as Lean have argued that they could help
avoid "Setoid Hell". What is the reason for using Setoids in the first
place? Does the move to extensional type theories based on HoTT (such
as cubical Agda) reduce the need for Setoids?
|*)

(*|
Answer (Floris van Doorn)
-------------------------

As Li-yao Xia's answer describes, setoids are used when we don't have
or don't want to use quotients.

In the HoTT book and in Lean quotients are (basically) axiomatized.
One difference between Lean and the HoTT book is that the latter has
many more higher inductive types, and Lean only has quotients and
(regular) inductive types. If we just restrict our attention to
quotients (set quotients in the HoTT book), it works the same in Lean
and in Book HoTT. In this case you just postulate that given a type
`A` and an equivalence `R` on `A` you have a quotient `Q`, and a
function `[-] : A -> Q` with the property `forall x y : A, R x y ->
[x] = [y]`. It comes with the following elimination principle: to
construct a function `g : Q -> X` for some type `X` (or hSet `X` in
HoTT) we need a function `f : A -> X` such that we can prove `forall x
y : A, R x y -> f x = f y`. This comes with the computation rule, that
states `forall x : A, g [x] === f x` (this is a definitional equality
in both Lean and Book HoTT).

The main disadvantage of this quotient is that it breaks canonicity.
Canonicity states that every closed term (that is, a term without free
variables) in (say) the natural numbers normalizes to either zero or
the successor of some natural number. The reason that this quotient
breaks canonicity is that we can apply the elimination principle for
`=` to the new equalities in a quotient, and a term like that will not
reduce. In Lean the opinion is that this doesn't matter, since in all
cases we care about we can still prove an equality, even though it
might not be a definitional equality.

Cubical type theory has a fancy way to work with quotients while
retaining canonicity. In CTT equality works differently, and this
means that higher inductive types can be introduced while keeping
canonicity. Potential disadvantages of CTT are that the type theory is
a lot more complicated, and that you have to embrace HoTT (and in
particular give up on proof irrelevance).
|*)

(*|
Answer (Jacques Carette)
------------------------

[The answers by Lia-yao Xia and Floris van Doorn are both excellent,
so I will try to augment them with additional information.]

Another view is that quotients, while used a lot in classical
mathematics, are perhaps not so great after all. Not taking quotients
but sticking to Groupoids is **exactly** where *non-commutative
geometry* starts from! It teaches us that some quotients are
incredibly badly behaved, and the last thing we want to do (in those
cases!) is to actually quotient. But that the thing itself is not so
bad, even quite good, if you treat it using the 'right' tools.

It is arguably also deeply embedded in all of category theory, where
one doesn't quotient out equivalent objects. Taking of 'skeletons' in
category theory is regarded to be in bad taste. The same is true of
strictness, and a host of other things, all of which boil down to
trying to squish things down that are better left as they are, as they
do no harm at all. We're just used to wanting 'uniqueness' to be
reflected in our representations - something we should just get over.

Setoid hell arises not because some coherences must be proven (you
need to prove them to show you have a proper equivalence, and again
whenever you define functions on raw representations instead of on the
quotiented version). It arises when you're forced to prove these
coherences again and again when defining functions that can't possibly
"go wrong". So Setoid hell is actually caused by a failure to provide
proper abstraction mechanisms.

In other words, if you're doing sufficient simple mathematics, where
quotients are well-behaved, then there should be some automation that
lets you work with that smoothly. Currently, in type theory, working
out exactly what that could look like, is ongoing research. Floris'
answer outlines well what one pitfall is: at some point, you give up
that `computations` will be well-behaved, and from then on, are forced
to do everything via proofs.
|*)

(*|
Answer (Li-yao Xia)
-------------------

Ideally one would certainly like to be able to treat arbitrary
equivalence relations as Leibniz equality (`eq`), enabling rewriting
in arbitrary contexts. That means to define the **quotient** of a type
by an equivalence relation.

I'm not an expert on the topic, but I've been wondering the same for a
while, and I think the reliance on setoids stems from the fact that
quotients are still a poorly understood concept in type theory.

1. Setoid Hell is where we're stuck when we don't have/want quotient
   types.
2. We can axiomatize quotient types, I believe (I could be mistaken)
   that's what Lean does.
3. We can develop a type theory which can naturally express quotients,
   that's what HoTT/Cubical TT do with higher inductive types.

Furthermore, quotient types (or my naive imagination of them) force us
to package programs and proofs together in a perhaps less-than-ideal
way: a function between two quotient types is a plain function
together with a proof that it respects the underlying equivalence
relation. While one can technically do that, this interleaving of
programming and proving is arguably indesirable because it makes
programs unreadable: one often seeks to either keep programs and
proofs in two completely separate worlds (so that mandates setoids,
keeping types separate from their equivalence relations), or to change
some representations so the program and the proof are one and the same
entity (so we might not even need to explicitly reason about
equivalences in the first place).
|*)
