(*|
##################
Coq Index Relation
##################

:Link: https://stackoverflow.com/q/47565160
|*)

(*|
Question
********

I'm defining an indexed inductive type in Coq:
|*)

Module Typ.
  (* My index -- a t is a `t H` or a `t Z`. *)
  Inductive hz : Set := H | Z.

  (* I'd like to use this relation to constrain Cursor and Arrow. *)
  (* E.g. one specialized Cursor has type `t H -> t Z -> t Z` *)
  Inductive maxHZ : hz -> hz -> hz -> Type :=
  | HZ : maxHZ H Z Z
  | ZH : maxHZ Z H Z
  | HH : maxHZ H H H.

  Inductive t : hz -> Type :=
  | Num : t H
  | Hole : t H
  | Cursor : t H -> t Z
  | Arrow : forall a b c, t a -> t b -> t c
  | Sum : forall a b c, t a -> t b -> t c.
End Typ.

(*|
How can I constrain my ``Arrow`` / ``Sum`` indices to be the same
shape as the ``maxHZ`` relation (short of creating more constructors,
like ``ArrowHZ : t H -> t Z -> t Z``).

----

**A:** Depending on your final use case, you could either create a
subtype of ``t`` and make ``Arrow`` satisfy the ``maxHZ`` predicate,
or alternatively, you could add the relation to the constructor
``Arrow : forall a b c, maxHZ a b c -> t a -> t b -> t c``. In all
cases, you want to make ``maxHZ`` irrelevant so it doesn't bug you in
proofs. Making it a boolean is likely a good idea.
|*)

(*|
Answer
******

One approach:
|*)

Reset Initial. (* .none *)
(* Bring the coercion is_true into scope *)
From Coq Require Import ssreflect ssrfun ssrbool.

Module Typ.
  (* My index -- a t is a `t H` or a `t Z`. *)
  Inductive hz : Set := H | Z.

  (* I'd like to use this relation to constrain Cursor and Arrow. *)
  (* E.g. one specialized Cursor has type `t H -> t Z -> t Z` *)
  Definition maxHZ (x y z : hz) : bool :=
    match x, y, z with
    | H, Z, Z
    | Z, H, Z
    | H, H, H => true
    | _, _, _ => false
    end.

  Inductive t : hz -> Type :=
  | Num : t H
  | Hole : t H
  | Cursor : t H -> t Z
  | Arrow : forall a b c, maxHZ a b c -> t a -> t b -> t c
  | Sum : forall a b c, maxHZ a b c -> t a -> t b -> t c.

(*| the other: |*)

  Reset t. (* .none *)
  Inductive t : hz -> Type :=
  | Num : t H
  | Hole : t H
  | Cursor : t H -> t Z
  | Arrow : forall a b c, t a -> t b -> t c
  | Sum : forall a b c, t a -> t b -> t c.

  Definition t_wf x (m : t x) : bool :=
    match m with
    | Arrow a b c _ _ => maxHZ a b c
    | Sum   a b c _ _ => maxHZ a b c
    | _ => true
    end.

  Definition t' x := { m : t x | t_wf x m }.
  (* This is automatically a subtype. *)
End Typ.

(*|
----

**Q:** Why do you redefine ``maxHZ`` as a function to ``bool`` instead
of keeping it like it is and having the constraint ``maxHZ a b c`` in
the ``Arrow`` constructor?

**A:** To get irrelevance for free, I don't want equality on ``t`` to
depend on the concrete shape / proof of the relation.
|*)
