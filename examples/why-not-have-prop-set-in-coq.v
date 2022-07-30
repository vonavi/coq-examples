(*|
###################################
Why not have ``Prop : Set`` in Coq?
###################################

:Link: https://proofassistants.stackexchange.com/q/1551
|*)

(*|
Question
********

My understanding of Coq is that ``Prop : Type_1``, ``Set : Type_1``,
and then ``Type_1 : Type_2``, ``Type_2 : Type_3``, etc.

So, at the bottom level, the world splits into two universes: ``Prop``
(impredicative) and ``Set`` (predicative, like all the other
``Type_i`` universes). My question is: why not just have ``Prop :
Type_0 : Type_1 : Type_2 : ...``, with ``Prop`` being impredicative as
it is today, and all the other levels would be predicative, also as is
the case today? Wouldn't that be simpler? Would cumulatively still
work?
|*)

(*|
Answer
******

As it often happens with Coq, the answer is *historical reasons*.

In the original version dating back from 1984, Coq was based on the
Calculus of Constructions, a barebone dependent type theory. In
particular, it did not feature inductive types. Instead, following the
PTS tradition, it had impredicative universes.

The introduction of inductive types did not change this state of
affair, and for a long time Coq had *two* impredicative universes,
``Prop`` and ``Set``. The difference between both lied in the fact
that the former was erased by extraction, but not the latter. This
phase separation had been around for a long time already.

When dealing with several impredicative universes, one has to be
extremely careful because proofs of ``False`` lurk around the corner.
In particular, ``Prop : Set`` when both are impredicative is enough be
a variant of Girard's system U⁻ and thus inconsistent. The Coq
developers of yore were well aware of this issue and relied on an
alternative hierarchy, so that ``Prop : Type`` and ``Set : Type``.

Now, at some point it was decided to make ``Set`` predicative by
default, for other somewhat related reasons. Indeed, impredicative
proof-relevant universes are very much inconsistent with many slightly
classical principles like excluded middle in ``Type`` or some forms of
choice. In particular and ironically, with an impredicative ``Set``,
Coq has no set-theoretical model (as in `Polymorphism is not
set-theoretic <https://hal.inria.fr/inria-00076261/document>`__).
Nowadays, ``Set`` is thus predicative except if the user opts in
impredicativity with a specific flag.

Impredicative set is essentially not used as of today, and really not
tested so it has fallen to bitrot. It is extremely likely that it is
not usable anymore, and there is an `evergreen discussion about its
removal <https://github.com/coq/coq/issues/9458>`__. Yet, since the
flag still exists Coq needs to at least pretend to avoid
inconsistencies when the user sets it, and therefore one cannot have
``Prop : Set``.

If the flag ever gets removed, maybe we can consider adding this rule,
but then there might be weird backwards incompatibilities. Therefore,
it is not even clear we will ever perform this change even in a
situation where it is perfectly sound.
|*)
