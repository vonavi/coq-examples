(*|
##################################
Recursive partial functions in Coq
##################################

:Link: https://stackoverflow.com/q/35696496
|*)

(*|
Question
********

I would like to know which is the best way to define a partial
recursive function in Coq.

Suppose that I want to define a function that returns the maximum
element of a list of natural numbers. However, we want this function
to be defined only for non-empty lists.

I've been trying the following:
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Fail Fixpoint MaxValueList (l : list nat | l <> []) : nat :=
  match l with
  | [n] => n
  | n :: l' => max n (MaxValueList l')
  end. (* .fails *)

(*|
However, this is not going to work since ``::`` is a constructor for
list and not for ``{l : list nat | l <> []}``.

My other attempt was using ``option``. In this case I tried the
following:
|*)

Fail Fixpoint MaxValueList (l : list nat) : option nat :=
  match l with
  | [] => None
  | [n] => Some n
  | n :: l' => max n (MaxValueList l')
  end. (* .fails *)

(*|
This did not work either since ``max : nat -> nat -> nat`` and
``MaxValueList l' : option nat``.

----

**A:** Personally, I would favor Arthur's choice of ``max`` with a
neutral element. One comment thou, the type ``T = {l : list nat | l <>
[]}`` is definitively speaking trouble, why? Because given two lists
``l1 l2 : T`` in order to prove their equality you must prove that the
``l <> []`` proofs are equal too, which is usually very hard...
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

Here's a possible solution to your problem:
|*)

Reset Initial. (* .none *)
Require Import Coq.Lists.List.
Import ListNotations.

Definition MaxValueListAux (n : nat) (l : list nat) : nat :=
  fold_left max l n.

Definition MaxValueListNE (l : list nat) : l <> [] -> nat :=
  match l with
  | []      => fun H => match H eq_refl with end
  | n :: l' => fun _ => MaxValueListAux n l'
  end.

(*|
Here, I've split the original ``MaxValueList`` into two parts: a
``MaxValueListAux`` function that computes the greatest element of a
list given a default value, and ``MaxValueListNE``, which is a wrapper
to the first function and takes a proof argument. This second function
merely discharges the impossible case and calls the first one with the
appropriate arguments; I'll explain how exactly this works shortly.
Because of this split, we don't run into the issue of constructing a
proof argument in the nonempty branch of ``MaxValueListNE``; the only
proof work that we have to do is to get rid of the empty case.

Notice that the second function is written in a weird way: instead of
declaring ``l <> []`` as another argument to ``MaxValueListNE``, I've
put it in the return type of that function. This is because of the way
dependent pattern matching works in Coq; roughly speaking, whenever
you need to combine information that you obtain on a ``match`` (such
as the fact that the ``l`` is empty on the ``[]`` branch) with
information that comes from "outside" the match (such as the proof of
``l <> []``), you need to make your ``match`` statement return a
function. This leads to a trick that Adam Chlipala calls the *convoy
pattern*, which you can learn more about `here
<http://adam.chlipala.net/cpdt/html/MoreDep.html>`__. Putting that
argument as part of the return type allows Coq to infer type
annotations that are required by the ``match`` statement.

So, how exactly does ``MaxValueListNE`` work? To understand this, we
must talk a little bit about how dependent pattern matching works in
Coq. As I mentioned earlier, we wrote this function in this particular
way so that Coq could infer some missing type annotations. But we can
add those by hand as well:
|*)

Reset MaxValueListNE. (* .none *)
Definition MaxValueListNE (l : list nat) : l <> [] -> nat :=
  match l return l <> [] -> nat with
  | []      => fun (H : [] <> [])      => match H eq_refl with end
  | n :: l' => fun (_ : n :: l' <> []) => MaxValueListAux n l'
  end.

(*|
When Coq reads this definition, it tries to type check the function,
and, in particular, make sure that every branch of the ``match``
returns an element of the type it promises to return. But when doing
so, it is allowed to replace every occurrence of the discriminee (in
this case, ``l``) by whatever value corresponds to that branch. In the
first branch above, this means replacing ``l`` by ``[]``, which in
turn implies that the returned function takes an argument of type ``[]
<> []``. Recall that in Coq, ``[] <> []`` is the same thing as ``[] =
[] -> False``. Since ``False`` has no constructors, we can get rid of
that contradictory branch by pattern-matching on ``H eq_refl``, where
``eq_refl`` is the only constructor of the equality type, and is taken
to have type ``[] = []`` in that particular case.

Now, it is worth noting that adding more type information is not
necessarily good. In the case of your function, I prefer to omit the
proof argument and write simply
|*)

Definition MaxValueList l := fold_left max l 0.

(*|
Note that ``0`` is a neutral element for ``max``, thus it makes sense
to return that value on the empty case. It allows us for instance to
prove a result like
|*)

Goal forall l1 l2,
    MaxValueList (l1 ++ l2) = max (MaxValueList l1) (MaxValueList l2).
Abort. (* .none *)

(*|
Of course, this doesn't work for every case: if we replaced ``max`` by
``min``, the above theorem wouldn't hold anymore. Still, I think it
would still be easier to program with and reason about a
``MinValueList`` function that works for arbitrary lists: if some
result about that function only works for nonempty elements, we can
add those hypotheses to our theorem:
|*)

Parameter MinValueList : list nat -> nat. (* .none *)
Goal forall l1 l2,
    l1 <> [] ->
    MinValueList (l1 ++ l2) = min (MinValueList l1) (MinValueList l2).
Abort. (* .none *)

(*|
This is how people usually define division in Coq. Instead of having a
partial function ``div : forall (n1 n2 : nat), n2 <> 0 -> nat``, we
write instead a total function ``div : nat -> nat -> nat``, and prove
*theorems* about that function assuming that its second argument is
not zero.
|*)

(*|
Answer (Rodrigo Ribeiro)
************************

One alternative is to use ``refine`` tactic to construct functions
using a theorem proving like style.

Whenever I need to construct terms with proofs (like your function) I
prefer to use definitions and refine tactic, since it provides a more
clear and easy way to automate proofs about propositions.

Below is a similar function that I have defined in a simple
formalisation. You can modify it easily to enforce the non-empty list
input requirement. The idea is to use refine tactic to provide the
structure of the function and the proof terms for function properties
are marked with holes ``_`` and latter filled with tactics.

.. coq:: none
|*)

Reset Initial.

Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Lia.

(*||*)

Definition max_list : forall l : list nat, {n | forall n', In n' l -> n > n'}.
  refine (fix max_list (l : list nat) : {n | forall n', In n' l -> n > n'} :=
            match l with
            | nil => exist _ 0 _
            | x :: l' =>
                match max_list l' with
                  exist _ x' _ =>
                    match le_gt_dec x x' with
                    | left _ => exist _ (S x') _
                    | right _ => exist _ (S x) _
                    end
                end
            end); clear max_list; simpl in *; intuition;
    try (match goal with
         | [H : context[In _ _ -> _],
            H1 : In _ _ |- _] => apply H in H1
         end); subst; lia.
Defined.

(*|
There are the so called `Program
<https://coq.inria.fr/distrib/current/refman/Reference-Manual027.html>`__
functionality that eases writing functions with dependent types. Maybe
is worth checking it. My experience is that it generate some
complicated hypothesis and, because of it, I prefer to use ``refine``.
|*)

(*|
Answer (larsr)
**************

The convoy pattern is a must to understand, but some of its reasoning
can be avoided by using ``Program``. ``Program`` also lets you write
more normal looking programs. I haven't really used it so I'll take
this chance to try it.
|*)

Reset Initial. (* .none *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Wf.

(*|
From ``False`` you can derive a value of any type that you need.
Useful in impossible branches in a match statement.
|*)

Definition IMPOSSIBLE {T} (f : False) :T := match f with end.

Program Fixpoint maxval (l : list nat) (H : l <> nil) {measure (length l)} : nat
  := match l with
     | []           => IMPOSSIBLE _
     | [a]          => a
     | a :: b :: l' => max a (maxval (b :: l') _)
     end.

(*|
EDIT: As ``eponier`` points out, if we include ``Require Import
Arith.`` before we define maxval, we will be done here. Otherwise we
will have to prove the remaining obligations, like this: (END EDIT)
|*)

Next Obligation.

(*|
Now we only have to prove that the recursion terminates. The goal is
|*)

  Show. (* .unfold .messages *)

(*| EDIT: ``eponier`` points out that this is easily proved by |*)

  apply measure_wf, PeanoNat.Nat.lt_wf_0.
Defined.
