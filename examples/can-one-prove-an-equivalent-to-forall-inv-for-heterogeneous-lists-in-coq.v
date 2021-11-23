(*|
Can one prove an equivalent to Forall_inv for heterogeneous lists in Coq?
=========================================================================

:Link: https://stackoverflow.com/questions/59178484/can-one-prove-an-equivalent-to-forall-inv-for-heterogeneous-lists-in-coq
|*)

(*|
Question
--------

Following Adam Chlipala's `definition
<http://adam.chlipala.net/cpdt/html/Cpdt.DataStruct.html#lab57>`_ of
heterogeneous lists, I wanted to define an equivalent of the
``Forall`` function on normal lists. This isn't too difficult, and you
end up with two constructors as usual. Now suppose that I know that a
fact is true about every element of a non-empty list. With normal
lists, I could use ``Forall_inv`` and ``Forall_inv_tail`` to assert
that it's true about the head and tail of the list.

I'd like to prove the equivalent for ``hForall`` as defined below,
starting with the head case. Looking at the source in `Lists/List.v
<https://github.com/coq/coq/blob/master/theories/Lists/List.v>`_, the
proof for normal lists is easy and runs by inversion on ``Forall (a ::
l)``. The equivalent for my ``hForall`` gives a mess of dependent
variables. Am I missing something obvious?
|*)

Require Import List.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons {a : A} {ls : list A} : B a -> hlist ls -> hlist (a :: ls).

  Section hForall.
    Variable P : forall a : A, B a -> Prop.

    Inductive hForall : forall {As : list A}, hlist As -> Prop :=
    | hForall_nil : hForall HNil
    | hForall_cons {a : A} {ls : list A} (x : B a) (hl : hlist ls)
      : P a x -> hForall hl -> hForall (HCons x hl).

    Lemma hForall_inv (a : A) (ls : list A) (x : B a) (hl : hlist ls)
      : hForall (HCons x hl) -> P a x.
    Proof.
      (* Help! *)
    Abort.
  End hForall.
End hlist.

(*|
Answer
------

Inductives indexed by indexed types lead to that kind of difficulty.

Alternatively, consider defining ``hForall`` as a ``Fixpoint``. Then
the inversion lemma follows by just unfolding the definition.
|*)

Reset hlist. (* .none *)
Section hForall'.

  Variable P : forall a, B a -> Prop.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons {a : A} {ls : list A} : B a -> hlist ls -> hlist (a :: ls).

  Fixpoint hForall' {As : list A} (hs : hlist As) : Prop :=
    match hs with
    | HNil => True
    | HCons x js => P _ x /\ hForall' js
    end.

  Lemma hForall'_inv (a : A) (ls : list A) (x : B a) (hl : hlist ls)
    : hForall' (HCons x hl) -> P a x.
  Proof.
    intros []; auto.
  Qed.

End hForall'.

(*|
----

Appendix
~~~~~~~~

Mostly for educational purposes, here's a few ways to prove that
inversion lemma for the original inductive definition of ``hForall``
(starting from the simpler to use).

One solution is the ``dependent destruction`` tactic, which also
automatically handles heterogeneous equalities, as opposed to
``destruct``. It is imported from the ``Program`` module:

.. coq:: none
|*)

Variable P : forall a, B a -> Prop.

Inductive hForall : forall {As : list A}, hlist As -> Prop :=
| hForall_nil : hForall HNil
| hForall_cons {a : A} {ls : list A} (x : B a) (hl : hlist ls)
  : P a x -> hForall hl -> hForall (HCons x hl).

(*||*)

Require Import Program.

Lemma hForall_inv (a : A) (ls : list A) (x : B a) (hl : hlist ls)
  : hForall (HCons x hl) -> P a x.
Proof.
  intros H. dependent destruction H. auto.
Qed.

(*|
The (minor) catch is that it uses some axioms about heterogeneous
equality:
|*)

Print Assumptions hForall_inv. (* .unfold *)

(*|
With a little more knowledge of how ``destruct`` works/dependent
pattern-matching, here's a proof without axioms.

There are some detailed explanations of dependent pattern-matching in
CPDT, but briefly the issue is that when we do
``destruct``/``inversion`` on ``hForall (HCons x hl)``, the index
``HCons x hl`` gets generalized before the case-split, so you get a
nonsensical case where it is replaced with ``HNil``, and a second case
with a *different* index ``HCons x0 hl0``, and a good way of
remembering the (heterogeneous) equality across that generalization is
a research-grade problem. You wouldn't need to mess with heterogeneous
equalities if the goal just got rewritten with those variables, and
indeed you can refactor the goal so that it explicitly depends on
``HCons x hl``, instead of ``x`` and ``hl`` separately, which will
then be generalized by ``destruct``:
|*)

Lemma hForall_inv' (a : A) (ls : list A) (x : B a) (hl : hlist ls)
  : hForall (HCons x hl) -> P a x.
Proof.
  intros H.
  change (match HCons x hl return Prop with
          (* for some reason you have to explicitly annotate the
             return type as Prop right here *)
          | HNil => True
          | HCons x _ => P _ x
          end).
      destruct H.
  - exact I.
  (* Replace [HCons x hl] with [HNil], the goal reduces to [True].
     (This is an unreachable case.) *)
  - assumption.

  (* Or, directly writing down the proof term. *)
  Restart.
  intros H.
  refine (match H in @hForall As hs return
                match hs return Prop with
                | HNil => True
                | HCons x _ => P _ x
                end
          with
          | hForall_nil => I
          | hForall_cons _ _ _ _ => _
          end).
  assumption.
Qed.

(*|
The Equations plugin probably automates that properly, but I haven't
tried.
|*)
