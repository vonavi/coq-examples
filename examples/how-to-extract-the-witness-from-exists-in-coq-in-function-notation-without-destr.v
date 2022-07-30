(*|
###########################################################################################
How to extract the witness from ``exists`` in Coq in function notation/without destructing?
###########################################################################################

:Link: https://proofassistants.stackexchange.com/q/1331
|*)

(*|
Question
********

Assuming I have some definition with a ``forall`` and an ``exists``
like so:
|*)

Definition fooable A B P := forall a : A, exists b : B, P a b.

(*|
Then on an intuitive level, I can for each ``(a : A)`` find a ``(b :
B)`` such that ``(P a b)`` holds, so it stands to reason that I can
build a function that generates the ``b`` from the ``a``. As Coq is
constructive, there has to be a witness for the ``b`` if I have
evidence for ``fooable``, so I am trying to define this function:
|*)

Definition fooify A B P (H : fooable A B P) : A -> B.

(*|
Using ``fun a => H a`` to get rid of the ``forall`` is easy enough,
but how can I extract the witness from the ``exists`` here? I've also
tried writing it as a proof and ``destruct``\ ing the ``exists``, but
as the goal is a ``Type``, not a ``Prop``, ``destruct`` errors.
|*)

(*|
Answer (Andrej Bauer)
*********************

In mathematics there are *two* kinds of existence:

1. The **concrete** or **informative existence** happens when we show
   that something exists by constructing a specific instance, which is
   then available.
2. The **abstract** or **non-informative existence** happens when we
   know that something exists by indirect means, or because the
   constucted witness has been hidden away from us by some mechanism.

An example that students come accross is this:

    **Theorem:** *There is a non-computable function*
    :math:`f:\mathbb{N} \rightarrow \mathbb{N}`.

*Abstract existence proof:* there are uncountably many function
:math:`\mathbb{N} \rightarrow \mathbb{N}` but only countably many
Turing machines, therefore some functions must be non-computable.
:math:`\square`

*Concrete existence proof:* we claim that the function
:math:`h:\mathbb{N} \rightarrow \mathbb{N}` defined by

.. math::

    h(n) = \begin{cases}
      1, \mbox{ if $n$-th Turing machine halts on input $n$}
      \\
      0, \mbox{ otherwise}.
    \end{cases}

is not computable. (Insert here the standard proof that :math:`h` is
not-computable.) :math:`\square`

I hope this conveys the idea clearly enough. First-order logic only
expresses the abstract existence. Martin-Löf type theory only
expresses the concrete existence.

Coq can express *both* kinds of existence. The abstract one is
``exists`` and the concrete one is ``sig``. So if you want to actually
extract witnesses, then you should be using ``sig``, not ``exists``.

In Coq ``sig (fun (x : A) => P x)`` is written in the more readable
notation ``{x : A | P x}``. Here is the extraction function you asked
for:
|*)

Definition extract {A B : Type} (P : A -> B -> Prop) :
  (forall a, { b : B | P a b }) -> { f : A -> B | forall a, P a (f a) } :=
  fun g => exist (fun f => forall a, P a (f a))
                 (fun a => proj1_sig (g a))
                 (fun a => proj2_sig (g a)).

(*|
It is possible to do violence to Coq and extract functions from the
wrong existence by postulating various choice principles (as in
`Coq.Logic.ChoiceFacts
<https://coq.inria.fr/library/Coq.Logic.ChoiceFacts.html>`__), but
it's just better to use the correct form of existence.

P.S. The difference between informative and non-informative facts
extends to all of logic and is not specific to existence. We may
distinguish between *informative* facts, where knowing a fact also
gives us the ability to inspect the *reason* for knowing it, and the
*non-informative* facts, where we simply know a fact, but have no
access to any reason as to why the fact holds. In Coq the
non-informative facts are in ``Prop``, whereas the informative ones
are in ``Type``.
|*)

(*|
Answer (kyo dralliam)
*********************

Extracting a function from a ``forall``/``exists`` statement is a
choice principle not derivable in Coq (at least not without axioms).
More precisely, this extraction could be derived out of
``FunctionalChoice_on`` (to get the existence of a function out of the
``forall``/``exists``) and ``ConstructiveIndefiniteDescription_on``
(to actually extract a function witnessing the existential) from the
module `Coq.Logic.ChoiceFacts
<https://coq.inria.fr/library/Coq.Logic.ChoiceFacts.html>`__ in the
"standard" library. That file also discuss in length the subtle
relationship between many different types of choice axioms.

----

**A:** Alternatively, you could replace the propositional existential
(``ex``) with one in ``Type`` (``sig``), from which you can extract a
function without any axiom.
|*)

(*|
Answer (Molossus Spondee)
*************************

As previously mentioned extracting a value from an existential is a
choice principle.

You can however extract a ``Prop`` or type squashed to ``Prop``.

The usual impredicative encoding of squashing is
|*)

Definition squash (A : Type) : Prop := forall B : Prop, (A -> B) -> B.

(*| But this can be a little awkward |*)

Reset Initial. (* .none *)
Variant squash (A : Type) : Prop :=
  | squash_intro : A -> squash A.

(*|
Is also awkward.

Writing the function
|*)

Definition proj_ex1 {A} {P : A -> _} : (exists x : A, P x) -> squash A.

(*|
Is then pretty simple.

Coq is pretty bare bones in terms of standard library and as far as I
know doesn't offer a version of ``squash`` or ergonomic tools for
working with it. (Edit: use ``inhabited``.) ``squash`` is
straightforwardly a monad and an applicative functor.

I generally find it easier to rework things to be in ``Set`` or
``Type`` instead of working around ``Prop`` though myself.

----

**A:** Coq does have a ``squash``. It is
|*)

Print inhabited. (* .unfold .messages *)

(*| and should be imported by default. |*)
