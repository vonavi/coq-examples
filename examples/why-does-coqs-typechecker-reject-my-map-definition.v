(*|
####################################################
Why does coq's typechecker reject my map definition?
####################################################

:Link: https://stackoverflow.com/questions/55969021/why-does-coqs-typechecker-reject-my-map-definition
|*)

(*|
Question
********

I try to experiment with list's definition. For example let's see this
definition:
|*)

Inductive list1 : Type -> Type :=
| nil1 : forall (A : Type), list1 A
| cons1 : forall (A : Type), A -> list1 A -> list1 A.

(*|
You might think that the definition above is equivalent to this:
|*)

Inductive list0 (A : Type) : Type :=
| nil0 : list0 A
| cons0 : A -> list0 A -> list0 A.

(*| Why this map: |*)

Fixpoint map0 {A : Type} {B : Type} (f : A -> B) (xs : list0 A) : list0 B :=
  match xs with
  | nil0 _ => nil0 B
  | cons0 _ v ys => cons0 B (f v) (map0 f ys)
  end.

(*| accepted, but this one is not: |*)

Fail Fixpoint map1 {A : Type} {B : Type} (f : A -> B) (xs : list1 A) :=
  match xs with
  | nil1 _ => nil1 B
  | cons1 _ v ys => cons1 B (f v) (map1 f ys)
  end.

(*| ? |*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

This is indeed a confusing aspect of datatype definitions. The problem
is that ``list1`` is *not* equivalent to ``list0``, because of how
*indices* and *parameters* are treated in these definitions. In Coq
jargon, an "index" means an argument declared to the right of the
colon, as in ``list1``. A "parameter", by contrast, is an argument
declared to the left of the colon, as ``A`` in ``list0``.

When you use an index, the return type of ``match`` expressions must
be generic with respect to the index. This can be seen in the type of
``list1_rec``, a combinator for writing recursive definitions on
lists:
|*)

Check list1_rec. (* .unfold *)

(*|
This type says that given a generic type ``P`` indexed by lists and an
element ``l : list1 A``, you can produce a result of type ``P A l`` by
telling Coq what to return on ``nil1`` and ``cons1``. However, the
type of the ``cons1`` branch (the third argument of ``list1``) says
that the branch must work not only for the ``A`` that appears in the
type of ``l``, but also for all *other* types ``A'``. Compare this to
the type of ``list0_rec``:
|*)

Check list0_rec. (* .unfold *)

(*|
The branch of ``cons0`` does not have the ``forall A`` bit, which
means that the branch only has to work for the type ``A`` in ``l :
list0 A``.

This makes a difference when writing a function such as ``map``. In
``map0``, we are allowed to apply ``f : A -> B`` because we know that
the argument of ``cons0`` has type ``A``. In ``map1``, the argument of
``cons1`` has a different generic type ``A'``, leading to this error
message:

.. coq:: unfold
|*)

Fail Fixpoint map1 {A : Type} {B : Type} (f : A -> B) (xs : list1 A) :=
  match xs with
  | nil1 A' => nil1 B
  | cons1 A' v ys => cons1 B (f v) (map1 f ys)
  end.

(*|
Answer (eponier)
****************

To be complete, you can define function ``map`` over ``list1``:
|*)

Fixpoint map1 {A : Type} {B : Type} (f : A -> B) (xs : list1 A) :=
  match xs with
  | nil1 A' => fun _ => nil1 B
  | cons1 A' v ys => fun f => cons1 B (f v) (map1 f ys)
  end f.

(*|
This is an example of the so-called `convoy pattern
<http://adam.chlipala.net/cpdt/html/MoreDep.html>`_. Usually, one
needs to add a ``return`` clause to the ``match`` construct so that it
typechecks, but here Coq is smart enough to infer it.

However, I certainly discourage using this definition of lists as it
will be cumbersome to use in similar cases.
|*)
