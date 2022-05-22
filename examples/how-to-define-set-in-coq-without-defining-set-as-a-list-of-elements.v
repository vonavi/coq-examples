(*|
###################################################################
How to define set in Coq without defining set as a list of elements
###################################################################

:Link: https://stackoverflow.com/q/36588263
|*)

(*|
Question
********

I am trying to define ``(1, 2, 3)`` as a set of elements in Coq. I can
define it using list as ``(1 :: (2 :: (3 :: nil)))``. Is there any way
to define set in Coq without using list.
|*)

(*|
Answer (ejgallego)
******************

There are basically four possible choices to be made when defining
sets in Coq depending on your constraints on the base type of the set
and computation needs:

- If the base type doesn't have decidable equality, it is common to
  use:
|*)

Parameter A : Type.
Definition set A := A -> Prop.
Definition cup (A B : A -> Prop) := fun x => A x /\ B x.

(*|
  basically, Coq's `Ensembles
  <https://coq.inria.fr/library/Coq.Sets.Ensembles.html>`__. This
  representation cannot "compute", as we can't even decide if two
  elements are equal.

- If the base data type has decidable equality, then there are two
  choices depending if extensionality is wanted:

  - Extensionality means that two sets are equal *in Coq's logic* iff
    they have the same elements, formally:

    .. code-block:: coq

        forall (A B : set T), (A = B) <-> (forall x, x \in A <-> x \in B).

    If extensionality is wanted, sets should be represented by a
    canonically-sorted duplicate-free structure, usually a list. A
    good example is Cyril's Cohen `finmap
    <https://github.com/Barbichu/finmap>`__ library. This
    representation however is very inefficient for computing as
    re-sorting is needed every time a set is modified.

  - If extensionality is not needed (usually a bad idea if proofs are
    wanted), you can use representations based on binary trees such as
    Coq's `MSet
    <https://coq.inria.fr/library/Coq.MSets.MSets.html>`__, which are
    similar to standard Functional Programming set implementations and
    can work efficiently.

- Finally, when the base type is finite, the set of all sets is a
  finite type too. The best example of this approach is IMO
  math-comp's `finset
  <http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.finset.html>`__,
  which encodes finite sets as the space of finitely supported
  membership functions, which is extensional, and forms a complete
  lattice.

----

**Q:** Why is Cyril's Cohen finmap inefficient?

**A:** A bit informally, the reason is because of the extensional
representation. A ``{fset T}`` needs to be "sorted" every time is
modified. On top of that, the "sorting" function is extremely
inefficient as it will enumerate all possible lists until it gets the
desired one. This helps to avoid having to equip ``T`` with an order
relation, as choice is guaranteed to be extensional on the predicate
(in this case, the library picks the first list satisfying, ``P x :=
perm_eq x (undup s)`` IIRC), which implies extensionality.

**Q:** Regarding your last bullet (base finite type) are you aware of
any more lightweight implementations besides ``finset``? It is a part
of ``sslreflect`` which is a heavy dependency, which in addition comes
with it's own language...

**A:** Well, you have Robbert Krebbers'
https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp, but I am not
sure it is more "lightweight", YMMV. ssreflect is surprisingly
lightweight for the power it packs.
|*)

(*|
Answer (Tiago Cogumbreiro)
**************************

The standard library of coq provides the following finite set modules:

1. `Coq.MSets <https://coq.inria.fr/library/Coq.MSets.MSets.html>`__
   abstracts away the implementation details of the set. For instance,
   there is `an implementation that uses AVL trees
   <https://coq.inria.fr/library/Coq.MSets.MSetAVL.html#>`__ and
   `another based on lists
   <https://coq.inria.fr/library/Coq.MSets.MSetList.html#>`__.
2. `Coq.FSets <https://coq.inria.fr/library/Coq.FSets.FSets.html>`__
   abstracts away the implementation details of the set; it is a
   previous version of ``MSets``.
3. `Coq.Lists.ListSet
   <https://coq.inria.fr/library/Coq.Lists.ListSet.html>`__ is an
   encoding of lists as sets, which I am including for the sake of
   completeness

Here is an example on how to define a set with ``FSets``:
|*)

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.

Module NSet := FSetAVL.Make Nat_as_OT.
(* Creates a set with only element 3 inside: *)
Check (NSet.add 3 NSet.empty).

(*|
Answer (Vinz)
*************

There are many encodings of sets in Coq (lists, function, trees, ...)
which can be finite or not. You should have a look at Coq's standard
library. For example the 'simplest' set definition I know is `this one
<https://coq.inria.fr/library/Coq.Sets.Ensembles.html>`__.
|*)
