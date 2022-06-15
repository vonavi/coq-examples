(*|
#################################
Coq: cannot unify inductive types
#################################

:Link: https://stackoverflow.com/q/50883392
|*)

(*|
Question
********

I am trying to represent multi-dimensional arrays as restricted
functions, and I am having a trouble with defining what seem to be a
primitive function.

Here are the definitions:
|*)

Require Export Fin.
Require Export PeanoNat.

Inductive ispace : nat -> Type :=
  Rect: forall d : nat, (Fin.t d -> nat) -> ispace d.

Inductive index : nat -> Type :=
  Idx: forall d : nat, (Fin.t d -> nat) -> index d.

Inductive bound_idx : forall d, index d -> ispace d -> Prop -> Type :=
  RectBoundIdx : forall d f_idx f_shp,
    bound_idx d (Idx d f_idx)
              (Rect d f_shp)
              (forall i, f_idx i < f_shp i).

Inductive array :
  forall d (is : ispace d),
    (forall idx pf, bound_idx d idx is pf -> nat) -> Type :=
  RectArray: forall (d:nat) sh_f val_f, array d (Rect d sh_f) val_f.

(*|
I define type families for rectangular index-spaces, for indices and
for an index that is bounded by a rectangular index-space. The array
type is a function from a restricted index-space to ``nat``.

Now, I am trying to construct an array from such a function, and Coq
tells me:
|*)

Fail Definition func_to_arr d is
                (af : forall idx pf, bound_idx d idx is pf -> nat) :=
       match is with
       | Rect d f => RectArray d f af
       end. (* .fails .unfold *)

(*|
So I am wondering, how can I pass this information to the above
definition, so that it becomes valid. Unless I misunderstand
something, the type of af contains all the necessary information to
reconstruct an array.
|*)

(*|
Answer
******

This issue is very common in dependently-typed programming with Coq.
To solve it, people usually use the *convoy pattern* described in
`CPDT <http://adam.chlipala.net/cpdt/>`__ by A. Chlipala (MoreDep
chapter, IIRC) and mentioned multiple time on Stackoverflow.

Here is how you can define the function.
|*)

Definition func_to_arr d is
           (af : forall idx pf, bound_idx d idx is pf -> nat) :=
  match is as is' in (ispace d1)
        return
        forall af' : forall idx pf,
            bound_idx d1 idx is' pf -> nat, array d1 is' af'
  with
  | Rect d2 f => fun af' => RectArray d2 f af'
  end af.

(*|
I'm doing dependent pattern-matching here, basically performing
"rewrites" of indices so Coq can see the connections between variables
that a human reader ususally takes for granted. You can read about the
constructions I used here in `extended pattern matching
<https://coq.inria.fr/refman/addendum/extended-pattern-matching.html#matching-objects-of-dependent-types>`__
section of the manual.

Incidentally, if you made ``d`` a *parameter* of your inductive types
instead of making it an *index*, you would not need to mess with
``d1``, ``d2`` and the ``in (ispace d1)`` would not be necessary. If
the choice was accidental, then you might want to take a look at the
`answer explaining the difference between those
<https://stackoverflow.com/questions/24600256/difference-between-type-parameters-and-indices/24601292#24601292>`__.
|*)
