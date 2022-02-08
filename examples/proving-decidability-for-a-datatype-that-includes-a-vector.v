(*|
##########################################################
Proving decidability for a datatype that includes a vector
##########################################################

:Link: https://stackoverflow.com/q/55335098
|*)

(*|
Question
********

I'm trying to work with a datatype that represents expressions in a
sort of universal algebra context. The usual way to express this in
(pen and paper) maths is that you have a set of function symbols, F,
together with an arity function. An expression is a tree where each
node is labelled with a function symbol and it has as many children as
its arity. In this particular example, I've also got a set of atomic
variables that get injected explicitly as terms.

It's pretty clear how to write this down with Coq (I've got a snippet
of code at the bottom), but I'd like to prove some sort of
decidability result. I've managed to prove decidability for vectors
("If I have decidability on ``A``, then I can get decidability on
``VectorDef.t A n``"), but I can't work out how to do the same for my
tree type.

I tried doing an explicit recursion over the structure of a tree, but
I ended up needing to call out to my "decidable vector" function,
which doesn't get past the termination checker. This is reasonable,
since the vector function expects to be given a discriminator for
arbitrary elements of its underlying type and this obviously doesn't
bottom out!

I can't work out how to tell Coq that (by induction) I have
decidability for some terms, and these are the only terms that appear
in the vectors in question. Is there a standard trick for doing this
sort of thing?

Below, the data types in question:
|*)

Require Vectors.VectorDef.

Definition vec := VectorDef.t.

Section VTree.
  (* If it helps, I have a definition for this function *)
  Variable dec_vec : forall A : Type,
    (forall x y : A, {x = y} + {x <> y}) ->
    forall (n : nat) (v v' : vec A n), {v = v'} + {v <> v'}.

  Variable V : Set.
  Variable F : Set.
  Variable a : F -> nat.

  Inductive VTree : Type :=
  | varTerm : V -> VTree
  | funTerm (f : F) (ts : vec VTree (a f)) : VTree.

  Section DecVTree.
    Hypothesis decV : forall x y : V, {x = y} + {x <> y}.
    Hypothesis decF : forall x y : F, {x = y} + {x <> y}.

    Definition decVTree : forall x y : VTree, {x = y} + {x <> y}.
      (* ??? *)
      Abort. (* .none *)

(*|
Answer (Li-yao Xia)
*******************

There are two challenging aspects to this problem.

1. Dependently typed programming with indexed types in Coq
2. Nested recursive types

Dependently typed programming with indexed types in Coq
=======================================================

By "indexed type" I am referring here specifically to inductive types
like ``Vector.t``, where the constructors refine some of the type
arguments. These arguments are called indices, and must appear between
``:`` and ``:=`` in the type signature:
|*)

Inductive Vector (A : Type) : nat (* <- index *) -> Type :=
| nil : Vector A 0
| cons : A -> forall n, Vector A n -> Vector A (S n).

(*|
Indexed inductive types are very useful to define propositions, where
the terms don't matter. But for actual data, the short story here is:
don't do it. It's technically possible, but it's a very deep rabbit
hole, and overall quite a pain to work with, in large part because
dependent pattern-matching in Coq is such an unintuitive construct.
For example, see this blogpost:
https://homes.cs.washington.edu/~jrw12/dep-destruct.html

A less extreme solution is to give up on other "dependently-typed"
aspects of this program. The next candidate on the chopping block here
is ``sumbool ({ _ } + { _ })``. If the functions (and parameters)
return bool instead, this makes them reasonably easy to define (\
*cough*, see next section). Proving their correctness is still a
problem but at least you have something to compute with.

Two general alternatives to inductive indexed types are:

- Just use the flat version (``list`` instead of ``vec``), giving up
  some "by construction" guarantees.
- Make the type a function of the indices as a ``Definition`` (or
  ``Fixpoint``), instead of ``Inductive``. Here we use ``unit`` and
  ``prod`` as building blocks for such types, but you may have to make
  up your own for more elaborate types. A lot of dependent
  pattern-matching will be necessary.
|*)

Reset Initial. (* .none *)
Fixpoint vec (A : Set) (n : nat) :=
  match n with
  | O => unit | S n => (A * vec A n)%type
  end.

(*|
You might also want to reconsider the representation of the language
you want to implement. For example, do you really want to represent
arities as explicitly as a function on symbols? (That could certainly
be the case.) For example, could you not restrict this to symbols of
arities 0, 1, 2?

Nested recursive types
======================

These are recursive types whose recursive occurrences are inside other
data types (which may be recursive). To simplify the discussion, to
unclutter the code, and because of the aforementioned issues with
dependent types in Coq, consider the following type using ``list``
instead of ``vec`` and with one fewer constructor:
|*)

Inductive LTree : Type :=
| funTerm : list LTree -> LTree.

(*|
You can define recursive functions on such a type with ``Fixpoint``,
but you have to be particularly careful about how recursive calls are
nested. Of course, this actually matters with any recursive type, but
the pattern is much more natural when the recursion is not nested, so
the problem is less noticeable.

Below is how we can decide equality for ``LTree``. We give up the
dependent ``sumbool``, returning a ``bool`` instead. The definition of
``dec_list`` is standard and generic.
|*)

Require Import List.
Import ListNotations.

Section List.

Context {A : Type} (decA : A -> A -> bool).

Fixpoint dec_list (l l' : list A) : bool :=
  match l, l' with
  | [], [] => true
  | a :: l0, a' :: l0' =>
    decA a a' && dec_list l0 l0'
  | _, _ => false
  end.

End List.

(*| Then equality of ``LTree`` looks innocent... |*)

Fixpoint decLTree (x y : LTree) : bool :=
  match x, y with
  | funTerm lx, funTerm ly =>
    dec_list decLTree lx ly
  end.

(*|
... but there are very subtle details that one needs to be aware of to convince Coq that the recursion is structurally decreasing.

The well-formedness of ``decLTree`` specifically depends in a very
delicate way on how ``dec_list`` uses its argument ``decA``, so
``dec_list`` must be a transparent definition:

1. It is only being applied to a subterm of the first list (you could
   make it the second if you want, with some ``struct`` annotations).
2. ``decA`` is bound *outside* of ``Fixpoint dec_list``. The function
   ``decLTree`` would not be well-formed if that line instead read
   ``Fixpoint dec_list {A : Type} (decA : A -> A -> bool)``.

It's also possible to package these tricks up by writing some general
recursion/induction schemes for ``LTree``/``VTree``.
|*)

(*|
Answer (Rupert Swarbrick)
*************************

While Li-yao made some useful points, the dependent types aren't that
bad! It turns out that the reason my previous script didn't work is
that I'd used ``Qed`` rather than ``Defined`` to finish my
decidability proof for vectors.

Here's a complete working proof:
|*)

Reset Initial. (* .none *)
Require Vectors.VectorDef.
Require Import Logic.Eqdep_dec.
Require Import PeanoNat.

Definition vec := VectorDef.t.

Section dec_vec.
  Variable A : Type.
  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.

  Definition dec_vec {n} (v v' : vec A n) : {v = v'} + {v <> v'}.
    refine (VectorDef.rect2 (fun _ x y => {x = y} + {x <> y})
                            (left (eq_refl))
                            (fun n v v' veq a a' => _)
                            v v').
    - destruct (decA a a') as [ eqaH | neaH ].
      + rewrite <- eqaH; clear eqaH a'.
        destruct veq as [ eqvH | nevH ].
        * rewrite <- eqvH. apply left. exact eq_refl.
        * apply right. intro consH. inversion consH.
          exact (nevH (inj_pair2_eq_dec nat Nat.eq_dec (vec A) n v v' H0)).
      + apply right.
        intro consH. inversion consH. contradiction.
  Defined.
End dec_vec.

Section VTree.
  Variable V : Set.
  Variable F : Set.
  Variable a : F -> nat.

  Inductive VTree : Type :=
  | varTerm : V -> VTree
  | funTerm (f : F) (ts : vec VTree (a f)) : VTree.

  Section DecVTree.
    Hypothesis decV : forall x y : V, {x = y} + {x <> y}.
    Hypothesis decF : forall x y : F, {x = y} + {x <> y}.

    Lemma varTerm_ne_funTerm v f ts : varTerm v <> funTerm f ts.
    Proof.
      intros eqH. inversion eqH.
    Qed.

    Fixpoint decVTree (x y : VTree) : {x = y} + {x <> y}.
      refine (match x, y with
              | varTerm v, varTerm v' => _
              | varTerm v, funTerm f ts => _
              | funTerm f ts, varTerm v => _
              | funTerm f ts, funTerm f' ts' => _
              end
             ).
      - destruct (decV v v') as [ eqH | neH ].
        + exact (left (f_equal varTerm eqH)).
        + enough (H: varTerm v <> varTerm v');
            try (exact (right H)).
          injection; tauto.
      - exact (right (varTerm_ne_funTerm v f ts)).
      - exact (right (not_eq_sym (varTerm_ne_funTerm v f ts))).
      - destruct (decF f f') as [ feqH | fneH ].
        + revert ts'. rewrite <- feqH. clear feqH; intro ts'.
          destruct (dec_vec VTree decVTree ts ts') as [ tseqH | tsneH ].
          * apply left. apply f_equal. exact tseqH.
          * apply right. intro funH. inversion funH.
            exact (tsneH (inj_pair2_eq_dec
                            F decF (fun f => vec VTree (a f)) f ts ts' H0)).
        + enough (H: funTerm f ts <> funTerm f' ts');
            try (exact (right H)).
          injection; tauto.
    Qed.
  End DecVTree.
End VTree.
