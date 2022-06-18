(*|
################################
Coq notation for multi type list
################################

:Link: https://stackoverflow.com/q/26755507
|*)

(*|
Question
********

Here is a contrived multi type list:
|*)

Inductive Apple : Set :=.
Inductive Pear : Set :=.

Inductive FruitList : Set :=
| Empty
| Cons_apple (a : Apple) (p : FruitList)
| Cons_pear (p : Pear) (p: FruitList).

Variable a : Apple.
Variable p : Pear.

Definition a_fruitList := Cons_apple a (Cons_pear p Empty).

(*|
Is there a way to define a list notation for this so that, for
example, ``a_fruitList`` could have been defined by ``[p,a]`` instead?
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

The problem is that your list has two cons constructors, whereas the
usual notation mechanism for recursive notations requires you to use
always the same constructors. Coercions can help you overcome part of
this problem:
|*)

Reset Initial. (* .none *)
Section ApplesAndPears.

  Variable Apple Pear : Set.

  Inductive FruitList : Set :=
  | Nil
  | ConsApple (a : Apple) (l : FruitList)
  | ConsPear (p : Pear) (l : FruitList).

  Inductive Fruit : Set :=
  | IsApple (a : Apple)
  | IsPear (p : Pear).

  Coercion IsApple : Apple >-> Fruit.
  Coercion IsPear : Pear >-> Fruit.

  Definition ConsFruit (f : Fruit) (l : FruitList) : FruitList :=
    match f with
    | IsApple a => ConsApple a l
    | IsPear p => ConsPear p l
    end.

  Notation "[ ]" := (Nil) (at level 0).
  Notation "[ x ; .. ; y ]" := (ConsFruit x .. (ConsFruit y Nil) ..) (at level 0).

  Variable a : Apple.
  Variable p : Pear.

  Definition a_fruitList := [ a ; p ].

End ApplesAndPears.

(*|
(By the way, I'm assuming that you really meant to write ``[ a ; p
]``, and not ``[ p ; a ]``. If you did mean to write ``[ p ; a ]``,
then you just have to use a ``SnocFruit`` function instead, that adds
the element to the end of the list. However, this would make the
problems explained later even worse.)

Now, we've defined a new function to replace the constructors, and can
use that function instead, by declaring the constructors of ``Fruit``
to be coercions.

This solution is not entirely satisfactory, of course, because the
term your notation produces makes reference to ``ConsFruit``, while
ideally it would be nice to have something that picks ``ConsApple`` or
``ConsFruit`` depending on the argument you give. I suspect there
isn't a way of doing this with the notation mechanism, but I could be
wrong.

This is one of the reasons why I would recommend you to use just the
``list`` type and declare another type such as ``Fruit`` to hold
``Apple`` and ``Pear`` instead of using two cons constructors, unless
you have a very good reason not to.
|*)

(*|
Answer (Virgile)
****************

As mentioned by `Arthur Azevedo De Amorim
<https://stackoverflow.com/a/26759446/1633665>`__, the issue is that
the ``Notation`` mechanism of Coq does not take the types of the
sub-expressions into account to discriminate between ``Cons_apple``
and ``Cons_pear``. However, you can use `Type Classes
<https://coq.inria.fr/distrib/current/refman/Reference-Manual022.html>`__
to do that:

.. coq:: none
|*)

Reset Initial.

Inductive Apple : Set :=.
Inductive Pear : Set :=.

Inductive FruitList : Set :=
| Empty
| Cons_apple (a : Apple) (p : FruitList)
| Cons_pear (p : Pear) (p: FruitList).

Variable a : Apple.
Variable p : Pear.

(*||*)

Class Cons_fruit (A : Set) := {
    CONS: A -> FruitList -> FruitList }.

Instance Cons_fruit_apple : Cons_fruit Apple := { CONS := Cons_apple }.
Instance Cons_fruit_pear : Cons_fruit Pear := { CONS := Cons_pear }.

Notation " [ x ; .. ; y ] " := (CONS x .. (CONS y Empty) .. ).

Definition test := [a; p; p; a].

(*|
We define here a type class ``Cons_fruit`` containing a single
function, and two instances, one for consing apples and one for
consing pears. We can then use the templated ``CONS`` function in the
notation, and Coq will select the appropriate instance when needed.

Note that this may result in less understandable error messages. For
instance, with
|*)

Fail Definition bad := [0; p]. (* .fails *)

(*| You will get |*)

Fail Definition bad := [0; p]. (* .unfold .messages *)
