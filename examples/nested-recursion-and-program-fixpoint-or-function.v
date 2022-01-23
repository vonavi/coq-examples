(*|
#########################################################
Nested recursion and ``Program Fixpoint`` or ``Function``
#########################################################

:Link: https://stackoverflow.com/q/46838928
|*)

(*|
Question
********

I'd like to define the following function using ``Program Fixpoint``
or ``Function`` in Coq:
|*)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Recdef.

Inductive Tree := Node : nat -> list Tree -> Tree.

Fixpoint height (t : Tree) : nat :=
  match t with
  | Node x ts => S (fold_right Nat.max 0 (map height ts))
  end.

Program Fixpoint mapTree (f : nat -> nat) (t : Tree)
        {measure (height t)} : Tree :=
  match t with
    Node x ts => Node (f x) (map (fun t => mapTree f t) ts)
  end.
Next Obligation.
Admitted.

(*|
Unfortunately, at this point I have a proof obligation ``height t <
height (Node x ts)`` without knowing that ``t`` is a member of ``ts``.

Similarly with ``Function`` instead of ``Program Fixpoint``, only that
``Function`` detects the problem and aborts the definition:
|*)

Fail Function mapTree (f : nat -> nat) (t : Tree) {measure height t} : Tree :=
  match t with
    Node x ts => Node (f x) (map (fun t => mapTree f t) ts)
  end. (* .fails .unfold .messages *)

(*|
I would expect to get a proof obligation of ``In t ts -> height t <
height (Node x ts)``.

Is there a way of getting that that does not involve restructuring the
function definition? (I know work-arounds that require inlining the
definition of ``map`` here, for example – I'd like to avoid these.)

Isabelle
========

To justify that expectation, let me show what happens when I do the
same in Isabelle, using the ``function`` command, which is (AFAIK)
related to Coq's ``Function`` command:

.. code-block:: isabelle

    theory Tree imports Main begin

    datatype Tree = Node nat "Tree list"

    fun height where
      "height (Node _ ts) = Suc (foldr max (map height ts) 0)"

    function mapTree where
      "mapTree f (Node x ts) = Node (f x) (map (λ t. mapTree f t) ts)"
    by pat_completeness auto

    termination
    proof (relation "measure (λ(f, t). height t)")
      show "wf (measure (λ(f, t). height t))" by auto
    next
      fix f :: "nat ⇒ nat" and x :: nat and ts :: "Tree list" and t
      assume "t ∈ set ts"
      thus "((f, t), (f, Node x ts))  ∈ measure (λ(f, t). height t)"
        by (induction ts) auto
    qed

In the termination proof, I get the assumption ``t ∈ set ts``.

Note that Isabelle does not require a manual termination proof here,
and the following definition works just fine:

.. code-block:: isabelle

    fun mapTree where
      "mapTree f (Node x ts) = Node (f x) (map (λ t. mapTree f t) ts)"

This works because the ``map`` function has a "congruence lemma" of
the form

.. code-block:: isabelle

    "xs = ys ⟹ (⋀x. x ∈ set ys ⟹ f x = g x) ⟹ map f xs = map g ys"

that the ``function`` command uses to find out that the termination
proof only needs to consider ``t ∈ set ts``.

If such a lemma is not available, e.g. because I define

.. code-block:: isabelle

    definition "map' = map"

and use that in ``mapTree``, I get the same unprovable proof
obligation as in Coq. I can make it work again by declaring a
congruence lemma for ``map'``, e.g. using

.. code-block:: isabelle

    declare map_cong[folded map'_def,fundef_cong]
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

In this case, you actually do not need well-founded recursion in its
full generality:
|*)

Reset Initial. (* .none *)
Require Import Coq.Lists.List.

Set Implicit Arguments.

Inductive tree := Node : nat -> list tree -> tree.

Fixpoint map_tree (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Node x ts => Node (f x) (map (fun t => map_tree f t) ts)
  end.

(*|
Coq is able to figure out by itself that recursive calls to
``map_tree`` are performed on strict subterms. However, proving
anything about this function is difficult, as the induction principle
generated for ``tree`` is not useful:
|*)

Check tree_ind. (* .unfold .messages *)

(*|
This is essentially the same problem you described earlier. Luckily,
we can fix the issue by proving our own induction principle with a
proof term.
|*)

Reset Initial. (* .none *)
Require Import Coq.Lists.List.
Import ListNotations.

Unset Elimination Schemes.
Inductive tree := Node : nat -> list tree -> tree.
Set Elimination Schemes.

Fixpoint tree_ind
         (P : tree -> Prop)
         (IH : forall (n : nat) (ts : list tree),
             fold_right (fun t => and (P t)) True ts ->
             P (Node n ts))
         (t : tree) : P t :=
  match t with
  | Node n ts =>
      let fix loop ts :=
        match ts return fold_right (fun t' => and (P t')) True ts with
        | [] => I
        | t' :: ts' => conj (tree_ind P IH t') (loop ts')
        end in
      IH n ts (loop ts)
  end.

Fixpoint map_tree (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Node x ts => Node (f x) (map (fun t => map_tree f t) ts)
  end.

(*|
The ``Unset Elimination Schemes`` command prevents Coq from generating
its default (and not useful) induction principle for ``tree``. The
occurrence of ``fold_right`` on the induction hypothesis simply
expresses that the predicate ``P`` holds of every tree ``t'``
appearing in ``ts``.

Here is a statement that you can prove using this induction principle:
|*)

Lemma map_tree_comp f g t :
  map_tree f (map_tree g t) = map_tree (fun n => f (g n)) t.
Proof.
  induction t as [n ts IH]. simpl. f_equal.
  induction ts as [|t' ts' IHts]; try easy.
  simpl in *. destruct IH as [IHt' IHts'].
  specialize (IHts IHts'). now rewrite IHt', <- IHts.
Qed.

(*|
Answer (Joachim Breitner)
*************************

In general, it might be advisable to avoid this problem. But if one
really wants to obtain the proof obligation that Isabelle gives you,
here is a way:

In Isabelle, we can give an external lemma that stats that ``map``
applies its arguments only to members of the given list. In Coq, we
cannot do this in an external lemma, but we can do it in the type. So
instead of the normal type of map

.. code-block:: coq

    forall A B, (A -> B) -> list A -> list B

we want the type to say "f is only ever applied to elements of the list":

.. code-block:: coq

    forall A B (xs : list A), (forall x : A, In x xs -> B) -> list B

(It requires reordering the argument so that the type of ``f`` can
mention ``xs``).

Writing this function is not trivial, and I found it easier to use a
proof script:

.. coq:: none
|*)

Reset Initial.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Wf.

Inductive Tree := Node : nat -> list Tree -> Tree.

Fixpoint height (t : Tree) : nat :=
  match t with
  | Node x ts => S (fold_right Nat.max 0 (map height ts))
  end.

(*||*)

Definition map {A B} (xs : list A) (f : forall x : A, In x xs -> B) : list B.
Proof.
  induction xs.
  - exact [].
  - refine (f a _ :: IHxs _).
    + left. reflexivity.
    + intros. eapply f. right. eassumption.
Defined.

(*| But you can also write it "by hand": |*)

Reset map. (* .none *)
Fixpoint map {A B} (xs : list A) :
  forall (f : forall x : A, In x xs -> B), list B :=
  match xs with
  | [] => fun _ => []
  | x :: xs =>
      fun f => f x (or_introl eq_refl) :: map xs (fun y h => f y (or_intror h))
  end.

(*|
In either case, the result is nice: I can use this function in
``mapTree``, i.e.
|*)

Program Fixpoint mapTree (f : nat -> nat) (t : Tree)
        {measure (height t)} : Tree :=
  match t with
    Node x ts => Node (f x) (map ts (fun t _ => mapTree f t))
  end.
Next Obligation.

(*|
and I don’t have to do anything with the new argument to ``f``, but it
shows up in the the termination proof obligation, as ``In t ts ->
height t < height (Node x ts)`` as desired. So I can prove that and
define ``mapTree``:
|*)

  simpl. apply Lt.le_lt_n_Sm.
  clear mapTree. induction ts; inversion_clear H.
  - subst. apply PeanoNat.Nat.le_max_l.
  - rewrite IHts by assumption.
    apply PeanoNat.Nat.le_max_r.
Qed.

(*|
It only works with ``Program Fixpoint``, not with ``Function``,
unfortunately.
|*)

(*|
Answer (Matthieu Sozeau)
************************

You can now do this with Equations and get the right elimination
principle automatically, using either `structural nested recursion
<http://mattam82.github.io/Coq-Equations/examples/Examples.nested_mut_rec.html>`__
or `well-founded recursion
<http://mattam82.github.io/Coq-Equations/examples/Examples.RoseTree.html>`__.
|*)
