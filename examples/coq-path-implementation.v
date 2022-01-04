(*|
###########################
Coq ``path`` implementation
###########################

:Link: https://stackoverflow.com/q/47948452
|*)

(*|
Question
********

This is a follow up to `Coq equality implementation
<https://stackoverflow.com/questions/47764368/coq-equality-implementation>`__
(though this question is self-contained).

I have a simple inductive type of trees (``t``) with a fixed set of
tags (``arityCode``), each with a fixed number of children. I have a
type (``path``) of paths into a tree. I'm trying to implement some
manipulations. In particular, I want to be able to move a cursor
around in a few directions. This seems pretty straightforward, but I'm
running into a roadblock.

This is all in the code, but a quick explanation of where I'm stuck:
To construct a ``there`` path, I need to produce a ``path (Vector.nth
v i)`` (a path in one of the children). But the only ``path``
constructors (``here`` and ``there``) produce a ``path (Node c v)``.
So in some sense I need to show the compiler that a path
simultaneously has type ``path (Node c v)`` and ``path (Vector.nth v
i)``, but Coq is not clever enough to compute ``(Vector.nth children
fin_n)`` -> ``Node c v``. How can I convince it that this is okay?
|*)

Require Coq.Bool.Bool. Open Scope bool.
Require Coq.Strings.String. Open Scope string_scope.
Require Coq.Arith.EqNat.
Require Coq.Arith.PeanoNat. Open Scope nat_scope.
Require Coq.Arith.Peano_dec.
Require Coq.Lists.List. Open Scope list_scope.
Require Coq.Vectors.Vector. Open Scope vector_scope.
Require Fin.

Module Export LocalVectorNotations.
Notation " [ ] " := (Vector.nil _) (format "[ ]") : vector_scope.
Notation " [ x ; .. ; y ] " :=
  (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) ..) : vector_scope.
Notation " [ x ; y ; .. ; z ] " :=
  (Vector.cons _ x _
               (Vector.cons _ y _ .. (Vector.cons _ z _ (Vector.nil _)) ..))
  : vector_scope.
End LocalVectorNotations.

Module Core.
  Module Typ.
    Set Implicit Arguments.

    Inductive arityCode : nat -> Type :=
    | Num   : arityCode 0
    | Hole  : arityCode 0
    | Arrow : arityCode 2
    | Sum   : arityCode 2.

    Definition codeEq (n1 n2 : nat) (l: arityCode n1) (r: arityCode n2)
      : bool :=
      match l, r with
      | Num, Num     => true
      | Hole, Hole   => true
      | Arrow, Arrow => true
      | Sum, Sum     => true
      | _, _         => false
      end.

    Inductive t : Type :=
    | Node : forall n, arityCode n -> Vector.t t n -> t.

    Inductive path : t -> Type :=
    | Here  : forall n (c : arityCode n) (v : Vector.t t n), path (Node c v)
    | There : forall n (c : arityCode n) (v : Vector.t t n) (i : Fin.t n),
        path (Vector.nth v i) -> path (Node c v).

    Example node1 := Node Num [].
    Example children : Vector.t t 2 := [node1; Node Hole []].
    Example node2 := Node Arrow children.

    (* This example can also be typed simply as `path node`, but we
       type it this way to use it as a subpath in the next example.
     *)
    Example here  : path (*node1*) (Vector.nth children Fin.F1) := Here _ _.
    Example there : path node2 := There _ children Fin.F1 here.

    Inductive direction : Type :=
    | Child : nat -> direction
    | PrevSibling : direction
    | NextSibling : direction
    | Parent : direction.

    Fail Fixpoint move_in_path
             (node : t)
             (dir : direction)
             (the_path : path node)
      : option (path node) :=
      match node with
        | @Node num_children code children =>
          match the_path with
          | There _ _ i sub_path =>
            move_in_path (Vector.nth children i) dir sub_path
          | Here _ _ =>
            match dir with
            | Child n =>
              match Fin.of_nat n num_children with
              | inleft fin_n =>
                let here : path (Vector.nth children fin_n) := Here _ _ in
                let there : path node := There _ children fin_n here in
                Some there
              | inright _ => None
              end
            | _ => None (* TODO handle other directions *)
            end
          end
      end. (* .fails .unfold *)

(*|
Answer
******

You could define a smart constructor for ``Here`` which does not have
any constraint on the shape of the ``t`` value it is applied to:
|*)

    Definition Here' (v : t) : path v := match v return path v with
                                         | Node c vs => Here c vs
                                         end.

(*|
You can then write:

.. code-block:: coq

    let here : path (Vector.nth children fin_n) := Here' _ in
|*)
