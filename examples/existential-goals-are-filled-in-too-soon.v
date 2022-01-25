(*|
########################################
Existential goals are filled in too soon
########################################

:Link: https://stackoverflow.com/q/51332966
|*)

(*|
Question
********

I have a ``Class`` containing both data and axioms. I want to build
another instance in proof mode, based on (1) an existing instance and
(2) some other input. I want to ``destruct`` this second input before
creating the new instance of the record.

The minimal ``Class`` that works as an example is shrunk from one in
`jwiegley/category-theory
<https://github.com/jwiegley/category-theory>`__:
|*)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Init.Datatypes.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.SetoidDec.

Generalizable All Variables.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "∘" (at level 40, left associativity).

Record Category := {
    obj : Type;

    uhom := Type : Type;
    hom : obj -> obj -> uhom where "a ~> b" := (hom a b);
    homset :> ∀ X Y, Setoid (X ~> Y);

    compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);

    compose_respects x y z :>
                     Proper (equiv ==> equiv ==> equiv) (@compose x y z);
  }.

(*| Suppose (2) is bool: |*)

Definition newCat (C : Category) (b : bool) : Category.
Proof.
  destruct b.
  - eapply Build_Category. Unshelve.

(*| At this point, ``obj`` is filled in with ``Type``: |*)

    Show. (* .unfold .messages *)

(*|
This behavior disappears if I remove the ``compose_respects`` axiom
(or use some other kind of ``Record`` without such a field). If I
change ``Category`` into a ``Class``, ``obj`` will be filled in as the
``obj`` of ``C``. It seems to have something to do with typeclass
resolution (the fact that the ``equiv``\ s have implicit typeclass
arguments?).

Is there someway to prevent these (or any!) variables from being
filled in with unification? The optimal result would be something like
``eapply``\ +\ ``Unshelve`` where no existentials are generated at
all, and I can fill in the record's fields as subgoals, in order.
|*)

(*|
Answer
******

It looks like ``simple notypeclasses refine {| obj := _ |}`` does the
trick.

- ``{| obj := _|}`` is record syntax that functions as shorthand for
  ``Build_Category _ _ _ _ _``.
- ``simple notypeclasses refine`` is all one tactic. It's a variant of
  ``notypeclasses refine`` that doesn't shelve goals and performs no
  reduction.
- Sadly there isn't a generic ``notypeclasses`` combinator, unlike
  ``unshelve``. There's just ``notypeclasses refine`` and ``simple
  notypeclasses refine``.

For debugging, you can use the (undocumented) ``Set Typeclasses
Debug``. This reveals that ``eapply Build_Category`` does resolve some
typeclasses, and ``refine {| obj := _|}`` is even worse.

As an aside, I don't think it makes sense to have ``Class Category``
without any type-level parameters - why would you ever want just any
category automatically inferred?
|*)
