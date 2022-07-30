(*|
#######################################################################
How to set defaults for implicit arguments when they can't be inferred?
#######################################################################

:Link: https://proofassistants.stackexchange.com/q/1013
|*)

(*|
Question
********

If I had a module declared as follows in file ``A.v``:
|*)

Section A.
  Context {X : Set}.
  Inductive abt := Abt_leaf (x : X) | Abt_node.
End A.

(*| And in another file, ``B.v``, I had: |*)

(* Require Import A. *)
Definition X := nat.
Inductive typ := Tpe_num | Typ_str.
Fail Definition typ_to_abt (t : typ) : abt (* @abt X *) := Abt_node. (* .fails .unfold *)

(*|
How could I let Coq know I **always** want ``abt`` to be ``@abt X`` in
``B.v``? The intent is to avoid explicitly specifying them using
``@``.
|*)

(*|
Answer
******

Not sure how robust that is, but you can do something quite nice using
`typeclasses
<https://coq.inria.fr/refman/addendum/type-classes.html>`__.
|*)

Reset Initial. (* .none *)
Section A.
  Class leaf_type := X : Type.
  Context `{L : leaf_type}.
  Inductive abt := Abt_leaf (x : X) | Abt_node.
End A.

Section B.
  #[local] Instance nat_leaf : leaf_type := nat.

  Inductive typ := Tpe_num | Typ_str.
  Definition typ_to_abt (t : typ) : abt := Abt_node.
End B.

(*|
To elaborate on what is happening here, we are first declaring a class
``leaf_type``, that Coq will try to infer on its own automatically
whenever it can, and ``abt`` makes use of that typeclass. In section
B, we put this to work: we declare ``nat`` as a ``#[local]`` instance,
so that whenever an implicit argument of type ``leaf_type`` is
encountered in that section, Coq will find the local instance ``nat``
and be happy with it. Once you close the section, the instance is gone
and you can declare another one later on.
|*)
