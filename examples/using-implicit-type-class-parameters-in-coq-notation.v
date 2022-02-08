(*|
####################################################
Using Implicit Type Class Parameters in Coq Notation
####################################################

:Link: https://stackoverflow.com/q/48394056
|*)

(*|
Question
********

I'm trying to wrap my head around type classes in Coq (I've dabbled
with it in the past, but I'm a far cry from being an experienced
user). As an exercise, I am trying to write a group theory library.
This is what I've come up with:
|*)

Class Group {S : Type} {op : S -> S -> S} := {
  id : S;

  inverse : S -> S;

  id_left {x} : op id x = x;
  id_right {x} : op x id = x;

  assoc {x y z} : op (op x y) z = op x (op y z);

  right_inv {x} : op x (inverse x) = id;
}.

(*|
I am particularly fond of the implicit ``S`` and ``op`` parameters
(assuming I understand them correctly).

Making some notation for inverses is easy:
|*)

Notation "- x" :=
  (@inverse _ _ _ x) (at level 35, right associativity) : group_scope.

(*|
Now, I would like to make ``x * y`` a shorthand for ``(op x y)``. When
working with sections, this is straightforward enough:
|*)

Section Group.
  Context {S} {op} {G : @Group S op}.

  (* Reserved at top of file *)
  Notation "x * y" := (op x y) : group_scope.
  (* ... *)
End Group.

(*|
However, since this is declared within a section, the notation is
inaccessible elsewhere. I would like to declare the notation globally
if possible. The problem I am running into (as opposed to ``inverse``)
is that, since ``op`` is an implicit parameter to ``Group``, it
doesn't actually exist anywhere in the global scope (so I cannot refer
to it by ``(@op _ _ _ x y)``). This problem indicates to me that I am
either using type classes wrong or don't understand how to integrate
notation with implicit variables. Would someone be able to point me in
the right direction?

Answer (25 Jan 2018)
====================

Based on `Anton Trunov's response
<https://stackoverflow.com/a/48398003/1451908>`__, I was able to write
the following, which works:
|*)

Reset Initial. (* .none *)
Reserved Notation "x * y" (at level 40, left associativity).

Class alg_group_binop (S : Type) := alg_group_op : S -> S -> S.

Delimit Scope group_scope with group.
Infix "*" := alg_group_op : group_scope.
Open Scope group_scope.

Class Group {S : Type} {op : alg_group_binop S} : Type := {
  id : S;

  inverse : S -> S;

  id_left {x} : id * x = x;
  id_right {x} : x * id = x;

  assoc {x y z} : (x * y) * z = x * (y * z);

  right_inv {x} : x * (inverse x) = id;
}.

(*|
Answer (Anton Trunov)
*********************

Here is how Pierre Castéran and Matthieu Sozeau solve this problem in
`A Gentle Introduction to Type Classes and Relations in Coq
<http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf>`__
(§3.9.2):

    A solution from *ibid*. consists in declaring a singleton type
    class for representing binary operators:
    |*)

    Class monoid_binop (A : Type) := monoid_op : A -> A -> A.

    (*|
    *Nota*: Unlike multi-field class types, ``monoid_op`` is not a
    constructor, but a transparent constant such that ``monoid_op f``
    can be δβ-reduced into ``f``.

    It is now possible to declare an infix notation:
    |*)

    Delimit Scope M_scope with M.
    Infix "*" := monoid_op: M_scope.
    Open Scope M_scope.

    (*|
    We can now give a new definition of ``Monoid``, using the type
    ``monoid_binop A`` instead of ``A -> A -> A``, and the infix
    notation ``x * y`` instead of ``monoid_op x y``:
    |*)

    Class Monoid (A : Type) (dot : monoid_binop A) (one : A) : Type := {
      dot_assoc : forall x y z : A, x * (y * z) = x * y * z;
      one_left : forall x, one * x = x;
      one_right : forall x, x * one = x
    }.
