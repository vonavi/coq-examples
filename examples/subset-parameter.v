(*|
################
Subset parameter
################

:Link: https://stackoverflow.com/q/5194117
|*)

(*|
Question
********

I have a set as a parameter:
|*)

Parameter Q : Set.

(*|
Now I want to define another parameter that is a subset of ``Q``.
Something like:

.. code-block:: coq

    Parameter F : subset Q.

How I can define that? I guess I can add the restriction later as an
axiom, but seems more natural to express it directly in the type of
``F``.
|*)

(*|
Answer
******

You can't express it directly.

It's misleading to think of objects in ``Set`` as mathematical sets.
``Set`` is the sort of datatypes, the same kinds of types that you
find in programming languages (except that Coq's types are very
powerful).

Coq doesn't have subtyping [1]_. If the two types ``F`` and ``Q`` are
distinct, then they are disjoint, as far as the mathematical model is
concerned.

The usual approach is to declare ``F`` as a completely related set,
and declare a canonical injection from ``F`` to ``Q``. You'll want to
specify any interesting property of that injection, beyond the
obvious.
|*)

Reset Initial. (* .none *)
Parameter Q : Set.
Parameter F : Set.
Parameter inj_F_Q : F -> Q.
Axiom inj_F_Q_inj : forall x y : F, inj_F_Q x = inj_F_Q y -> x = y.
Coercion inj_F_Q : F >-> Q.

(*|
That last line declares a coercion from ``F`` to ``Q``. That lets you
put an object of type ``F`` wherever the context requires the type
``Q``. The type inference engine will insert a call to ``inj_F_Q``.
You will need to write the coercion explicitly occasionally, since the
type inference engine, while very good, is not perfect (perfection
would be mathematically impossible). There is a chapter on coercions
in the Coq reference manual; you should at least skim through it.

Another approach is to define your subset with an extensional
property, i.e. declare a predicate ``P`` on the set (the type) ``Q``
and define ``F`` from ``P``.
|*)

Reset Initial. (* .none *)
Parameter Q : Set.
Parameter P : Q -> Prop.
Definition G := sig P.
Definition inj_G_Q : G -> Q := @proj1_sig Q P.
Coercion inj_G_Q : G >-> Q.

(*|
``sig`` is a specification, i.e. a weak sum type, i.e. a pair
consisting of an object and a proof that said object has a certain
property. ``sig P`` is eta-equivalent to ``{x | P x}`` (which is
syntactic sugar ``sig (fun x => P x)``). You have to decide whether
you prefer the short or the long form (you need to be consistent). The
``Program`` vernacular is often useful when working with weak sums.

.. [1] There is subtyping in the module language, but that's not
   relevant here. And coercions fake subtyping well enough for many
   uses, but they're not the real thing.
|*)
