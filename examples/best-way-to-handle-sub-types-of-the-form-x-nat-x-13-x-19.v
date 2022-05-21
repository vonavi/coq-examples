(*|
################################################################################
Best way to handle (sub) types of the form ``{ x : nat | x >= 13 /\ x <= 19 }``?
################################################################################

:Link: https://stackoverflow.com/q/37897316
|*)

(*|
Question
********

Coq would let me define this:
|*)

Definition teenagers : Set := { x : nat | x >= 13 /\ x <= 19 }.

(*| and also: |*)

Variable Julia : teenagers.

(*| but not: |*)

Fail Example minus_20 : forall x : teenagers, x < 20. (* .fails *)

(*| or: |*)

Fail Example Julia_fact1 : Julia > 12. (* .fails *)

(*|
This is because Julia (of type ``teenagers``) cannot be compared to 12
(``nat``).

**Q:** How should I inform Coq that Julia's support type is ``nat`` so
that I can write anything useful about her?

**Q':** My definition of teenagers seems like a dead end; it is more
declarative than constructive and I seem to have lost inductive
properties of ``nat``. How can I show up its inhabitants? If there is
no way, I can still stick to ``nat`` and work with ``Prop`` and
functions. (newbie here, less than one week self learning with
`Pierce's SF
<https://www.cis.upenn.edu/~bcpierce/sf/current/index.html>`__).
|*)

(*|
Answer
******

The pattern you are using in ``teenagers`` is an instance of the
"subType" pattern. As you have noted, a ``{ x : nat | P x }`` is
different from ``nat``. Currently, Coq provides little support to
handle these kind of types effectively, but if you restrict to
"well-behaved" classes of ``P``, you can actually work in a reasonable
way. [This should really become a Coq FAQ BTW]

In the long term, you may want to use special support for this
pattern. A good example of such support is provided by the math-comp
library ``subType`` interface.

Describing this interface is beyond your original question, so I will
end with a few comments:

- In your ``minus_20`` example, you want to use the *first projection*
  of your teenagers datatype. Try ``forall x : teenagers, proj1_sig x
  < 20``. Coq can try to insert such projection automatically if you
  declare the projection as a ``Coercion``:
|*)

Reset Initial. (* .none *)
Require Import Lia.

Definition teenagers : Set := { x : nat | x >= 13 /\ x <= 19 }.

Coercion teen_to_nat := fun x : teenagers => proj1_sig x.

Implicit Type t : teenagers.

Lemma u t : t < 20.
Proof. now destruct t; simpl; lia. Qed.

(*|
- As you have correctly observed, ``{ x : T | P x }`` is not the same
  in Coq than ``x``. In principle, you cannot transfer reasoning from
  objects of type ``T`` to objects of type ``{ x : T | P x }`` as you
  must also reason in addition about objects of type ``P x``. But for
  a wide class of ``P``, you can show that the ``teen_to_nat``
  projection is injective, that is:

  .. code-block:: coq

      forall t1 t2, teen_to_nat t1 = teen_to_nat t2 -> t1 = t2.

  Then, reasoning over the base type can be transferred to the
  subtype. See also: `Inductive subset of an inductive set in Coq
  <https://stackoverflow.com/questions/35290012/inductive-subset-of-an-inductive-set-in-coq/35300521#35300521>`__

**[edit]:** I've added a couple typical examples of subTypes in
math-comp, as I think they illustrate well the concept:

- Sized lists or ``n.-tuples``. A list of length ``n`` is represented
  in math-comp as a pair of a single list plus a proof of size, that
  is to say ``n.-tuple T = { s : seq T | size s == n}``. Thanks to
  injectivity and coertions, you can use all the regular list
  functions over tuples and they work fine.
- Bounded natural or ordinals: similarly, the type ``'I_n = { x : nat
  | x < n }`` works almost the same than a natural number, but with a
  bound.

----

**A:** CPDT covers subset types, starting from `this chapter
<http://adam.chlipala.net/cpdt/html/Cpdt.Subset.html>`__.

**A:** I heard something is on the works... There will be a tutorial
soon at ITP soon thou:
https://github.com/math-comp/wiki/wiki/tutorial-itp2016 which can be
run in the browser, also this provides some exercises
https://team.inria.fr/marelle/en/advanced-coq-winter-school-2016 but
it is geared towards math.
|*)
