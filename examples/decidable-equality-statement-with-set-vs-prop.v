(*|
Decidable equality statement with Set vs. Prop
==============================================

https://stackoverflow.com/questions/69710435/decidable-equality-statement-with-set-vs-prop
|*)

(*|
Question
--------

When looking at results for types with decidable equality (especially
in `Eqdep_dec
<https://coq.inria.fr/library/Coq.Logic.Eqdep_dec.html>`_) there are
some of the results that (for a type `A`) require
|*)

Section EqdepDec. (* .none *)
Variable A : Type. (* .none *)
Variable eq_dec : forall x y : A, x = y \/ x <> y.
End EqdepDec. (* .none *)

(*| whereas some require |*)

Module Type DecidableSet. (* .none *)
Parameter A : Set. (* .none *)
Axiom eq_dec : forall x y : A, {x = y} + {x <> y}.
End DecidableSet. (* .none *)

(*|
It is my impression that it is the last one that is referred to as
*decidable equality*, but I am very much uncertain what the difference
is. I know that `x = y \/ x <> y` in `Prop` and `{x = y} + {x <> y}`
is in `Set`, and I can prove the first one from the second one but not
the other way around. As far as I understand it, it is because I am
not allowed to construct values of type `Prop` from values of type
`Set`.

Can anyone tell what the difference between the two are? Are there
some example of a type for which the first statement can be proved but
not the second. Also, is it true that the version with `{x = y} + {x
<> y}` is what is referred to as decidable equality?
|*)

(*|
Answer
------

You are correct that the latter definition, the one which lives in
`Set`, is referred to as *decidable equality*.

Intuitively, we interpret objects in `Set` as programs, and objects in
`Prop` as proofs. So the decidable equality type is the type of a
function which takes any two elements of some type `A` and decides
whether they are equal or unequal.

The other statement is slightly weaker. It describes the proposition
that any two elements of `A` are either equal of unequal. Notably, we
would not be able to inspect *which* outcome is the case for specific
values of `x` and `y`, at least outside of case analysis within a
proof. This is the result of the `Prop` elimination restriction that
you alluded to (although you got it backwards: one is not allowed to
construct values of sort `Set`/`Type` by eliminating/matching on an
element of sort `Prop`).

Without adding axioms, the `Prop` universe is constructive, so I
believe that there would not be any types `A` such that equality is
undecidable but the propositional variant is provable. However,
consider the scenario in which we make the `Prop` universe classical
by adding the following axiom:
|*)

Axiom classic : forall P, P \/ ~P.

(*|
This would make the propositional variant trivially provable for any
type `A`, while the decidable equality may not be realizable.

Note that our axiom is a proposition. Intuitively, it makes sense that
either a proposition or its negation must hold. If we hadn't made this
a `Prop` (for example, if we axiomatized `forall P, {P} + {~P}`), then
we would likely not accept the axiom, since it would instead be
declaring the existence of a universal decision procedure.

That was a bit of a digression, but hopefully it demonstrated some
differences in our interpretation of `Prop`'s and `Set`'s.
|*)
