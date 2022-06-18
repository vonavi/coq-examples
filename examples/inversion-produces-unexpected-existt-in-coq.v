(*|
###############################################
Inversion produces unexpected ``existT`` in Coq
###############################################

:Link: https://stackoverflow.com/q/24720137
|*)

(*|
Question
********

Here is an inductive type ``pc`` that I am using in a mathematical
theorem.
|*)

Inductive pc (n : nat) : Type :=
| pcs : forall m : nat, m < n -> pc n
| pcm : pc n -> pc n -> pc n.

(*|
And another inductive type ``pc_tree``, which is basically a binary
tree that contains one or more ``pc``\ s. ``pcts`` is a leaf node
constructor that contains a single ``pc``, and ``pctm`` is an internal
node constructor that contains multiple ``pc``\ s.
|*)

Inductive pc_tree : Type :=
| pcts : forall n : nat, pc n -> pc_tree
| pctm : pc_tree -> pc_tree -> pc_tree.

(*|
And an inductively defined proposition ``contains``. ``contains n x
t`` means that the tree ``t`` contains at least one ocurrence of ``x :
pc n``.
|*)

Inductive contains (n : nat) (x : pc n) : pc_tree -> Prop :=
| contain0 : contains n x (pcts n x)
| contain1 : forall t s : pc_tree, contains n x t -> contains n x (pctm t s)
| contain2 : forall t s : pc_tree, contains n x t -> contains n x (pctm s t).

(*| Now, the problematic lemma I need to prove: |*)

Lemma contains_single_eq : forall (n : nat) (x y : pc n),
    contains n x (pcts n y) -> x = y.
Abort. (* .none *)

(*|
What the lemma means is really simple: if a tree that has a single
leaf node containing ``y : pc n`` contains some ``x : pc n``, it
follows that ``x = y``. I thought I should be able to prove this with
a simple ``inversion`` on ``contains``. So When I wrote
|*)

Lemma contains_single_eq : forall (n : nat) (x y : pc n),
    contains n x (pcts n y) -> x = y.
Proof.
  intros n x y H. inversion H.

(*|
I was expecting to get ``x = y`` as an hypothesis in the context.
Here's what I got instead:
|*)

  Show. (* .unfold .messages *)
Abort. (* .none *)

(*|
``H1`` is quite different from what I expected. (I've never seen
``existT`` before.) All I care about is that I prove
``contains_single_eq``, but I'm not sure how to use ``H1`` for it, or
whether it is usable at all.

----

**A:** ``{x : T & P x}`` is a dependent sum like ``T * P`` is a
nondependent sum. ``@existT T P x H : {x : T & P x}`` like ``@pair T P
x H : T * P``. ``exists x : T, P x, {x : T | P x}``, and ``{x : T & P
x}`` are very similar. Use the ``Print ex.``, ``Print sig.``, and
``Print sigT.`` commands.
|*)

(*|
Answer
******

This is a recurring problem when doing inversion on things that
involve dependent types. The equality that is generated over
``existT`` just means that Coq cannot invert the equality ``pcts n x =
pcts n y`` like it would for normal types. The reason for that is that
the index ``n`` that appears on the types of ``x`` and ``y`` cannot be
generalized when typing the equality ``x = y``, which is required for
doing the inversion.

``existT`` is the constructor for the dependent pair type, which
"hides" the ``nat`` index and allows Coq to avoid this problem in the
general case, producing a statement which is slightly similar to what
you want, although not quite the same. Fortunately, for indices that
have a decidable equality (such as ``nat``), it is actually possible
to recover the "usual" equality using theorem ``inj_pair2_eq_dec`` in
the `standard library
<http://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Eqdep_dec.html>`__.
|*)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.

Lemma contains_single_eq :
  forall (n : nat) (x y : pc n), contains n x (pcts n y) -> x = y.
Proof.
  intros n x y H. inversion H.
  apply inj_pair2_eq_dec in H1.
  - trivial.
  - apply eq_nat_dec.
Qed.
