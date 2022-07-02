(*|
##########################################################################################
Decoupling the data to be manipulated from the proofs that the manipulations are justified
##########################################################################################

:Link: https://stackoverflow.com/q/12366005
|*)

(*|
Question
********

I have a type of lists whose heads and tails must be in a certain
sense "compatible":
|*)

Inductive tag := A | B. (* Just an example *)

Inductive element : tag -> tag -> Set :=
| AA : element A A
| AB : element A B
| BB : element B B. (* Also just an example *)

Inductive estack : tag -> tag -> Set :=
| ENil  : forall     t,                              estack t t
| ECons : forall r s t, element r s -> estack s t -> estack r t.

(*|
However, I do not like this code very much, for the following reasons:

1. It is not *modular*: The ad-hoc list data constructors are
   intrinsically coupled with the proofs that the heads and tails are
   compatible --- the tags.
2. It does not favor *code reuse*: I am forced to redefine the usual
   list functions (such as list concatenation) and re-prove the usual
   list theorems (such as the associativity of list concatenation).

I have a different approach in mind, which consists of three steps:

1. Defining a single type of tagged elements (as opposed to a family
   of tagged types of elements):
|*)

Inductive taggedElement := Tagged : forall t1 t2,
      element t1 t2 -> taggedElement.

(*|
2. Defining the type of arbitrary (that is, either valid or invalid)
   lists of tagged elements:
|*)

Definition taggedElementStack := list taggedElement.

(*|
3. Defining a *valid* list of tagged elements as a tuple whose
   elements are an arbitrary list of tagged elements *and* a proof
   that the elements are compatible with the adjacent ones.
|*)

(* I have no idea how to do this in Coq, hence the question!
 *
 * I am going to use pseudomathematical notation. I am not well versed in either
 * mathematics or theoretical computer science, so please do not beat me with a
 * stick if I say something that is completely bogus!
 *
 * I want to construct the type
 *
 *     (tes : taggedElementStack, b : proof that P(tes) holds)
 *
 * where P(tes) is a predicate that is only true when, for every sublist of tes,
 * including tes itself, the heads and tails are compatible.
 *)

(*| How would I perform the third step in Coq? |*)

(*|
Answer
******

Look at your ``estack``, what does it do? Generalize! ``element`` is
just a relation (``A -> A -> Set``), ``tag`` is just a ``Set``. What
do you get?
|*)

Definition Rel I := I -> I -> Set. (* .none *)
Inductive RTList {I : Set} (X : Rel I) : Rel I :=
| RTNil  : forall {i : I}, RTList X i i
| RTCons : forall {i j k : I},    X i j -> RTList X j k -> RTList X i k.

(*|
(``Rel`` ist just a Definition with ``Rel I := I -> I -> Set``.)

Reflexive-transitive closure! That is common, reusable and modular. Or
so you'd think.

The only implementation I found in Coq's libs is in
``Coq.Relations.Relation_Operators``, named `clos_refl_trans
<http://coq.inria.fr/stdlib/Coq.Relations.Relation_Operators.html#clos_refl_trans>`__,
differently structured and locked into ``Prop`` (all according to the
docs, didn't try it).

You'll probably have to re-implement that or find a library somewhere.
At least, you'll only have to do this once (or up to three times for
``Set``, ``Prop`` and ``Type``).

----

Your other idea will probably be harder to manage. Look at `NoDup
<http://coq.inria.fr/stdlib/Coq.Lists.List.html#NoDup>`__ for
something that's similar to your description, you might be able to
reuse the pattern. If you really want that. `NoDup
<http://coq.inria.fr/stdlib/Coq.Lists.List.html#NoDup>`__ uses `In
<http://coq.inria.fr/stdlib/Coq.Lists.List.html#In>`__, which is a
function that checks if an element is in a list. The last time I tried
using it, I found it considerably harder to solve proofs involving
``In``. You can't just ``destruct`` but have to apply helper lemmas,
you have to carefully unfold exactly ``$n`` levels, folding back is
hard etc. etc. I'd suggest that unless it's truly necessary, you'd
better stick with data types for ``Prop``\ s.
|*)
