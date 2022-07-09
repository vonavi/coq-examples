(*|
####################################################
Difference between parameters and members of a class
####################################################

:Link: https://stackoverflow.com/q/70112873
|*)

(*|
Question
********

I am new to Coq and was wondering what is the difference between the
following things:
|*)

Class test (f g : nat -> nat) := {
    init : f 0 = 0 /\ g 0 = 0;
  }.

(*| and |*)

Reset Initial. (* .none *)
Class test := {
    f : nat -> nat;
    g : nat -> nat;
    init : f 0 = 0 /\ g 0 = 0;
  }.

(*|
Could anyone provide an explanation?
|*)

(*|
Answer (Ana Borges)
*******************

The difference between them is referred to as bundling.
|*)

Reset Initial. (* .none *)
Class test (f g : nat -> nat) := {
    init:   f 0 = 0 /\ g 0 = 0;
  }.

(*| is unbundled, and |*)

Reset Initial. (* .none *)
Class test := {
    f : nat -> nat;
    g : nat -> nat;
    init : f 0 = 0 /\ g 0 = 0;
  }.

(*|
is bundled.

The advantage of bundling is that you don't need to always provide
``f`` and ``g``. The advantage of unbundling is that you can have
different instances of the same class sharing the same ``f`` and
``g``. If you bundle them, Coq will not be easily convinced that
different instances share parameters.

You can read more about this in `Type Classes for Mathematics in Type
Theory
<https://www.researchgate.net/publication/48202776_Type_Classes_for_Mathematics_in_Type_Theory>`__.
|*)

(*|
Answer (Maëlan)
***************

To complement Ana's excellent answer, here is a practical difference:

- the unbundled version (call it ``utest``) allows you to write the
  logical statement ``utest f g`` about a specific pair of functions
  ``f`` and ``g``,
- whereas the bundled version (call it ``btest``) allows you to state
  that there exists a pair of functions which satisfies the
  properties; you can later refer to these functions by the projection
  names ``f`` and ``g``.

So, roughly speaking:

- ``btest`` is "equivalent" to ``∃ f g, utest f g``;
- ``utest f' g'`` is "equivalent" to ``btest`` ∧ "the ``f`` (resp.
  ``g``) in the aforementioned proof of btest is equal to ``f'``
  (resp. ``g'``)".

More formally, here are the equivalences for a minimal example (in
this code, the notation ``{ x : A | B }`` is a **dependent pair**
type, i.e. the type of ``(x, y)`` where ``x : A`` and ``y : B`` and
the type ``B`` depends on the value ``x``):
|*)

Reset Initial. (* .none *)
(* unbundled: *)
Class utest (x : nat) : Prop := {
    uprop : x = 0;
  }.

(* bundled: *)
Class btest : Type := {
    bx : nat;
    bprop : bx = 0;
  }.

(* [btest] is equivalent to: *)

Goal { x : nat | utest x } -> btest.
Proof.
  intros [x u]. econstructor. exact (@uprop x u).
Qed.

Goal btest -> { x : nat | utest x }.
Proof.
  intros b. exists (@bx b). constructor. exact (@bprop b).
Qed.

(* [utest x] is equivalent to: *)

Goal forall x, { b : btest | @bx b = x } -> utest x.
Proof.
  intros x [b <-]. constructor. exact (@bprop b).
Qed.

Goal forall x, utest x -> { b : btest | @bx b = x }.
Proof.
  intros x u. exists {| bx := x ; bprop := @uprop x u |}. reflexivity.
Qed.

(* NOTE: Here I've explicited all implicit arguments; in fact, you
   can let Coq infer them, and write just [bx], [bprop], [uprop]
   instead of [@bx b], [@bprop b], [@uprop x u]. *)

(*|
In this example, we can also observe a difference with respect to
computational relevance: ``utest`` can live in ``Prop``, because its
only member, ``uprop``, is a proposition. On the other hand, I cannot
really put ``btest`` in ``Prop``, because that would mean that *both*
``bx`` and ``bprop`` would live in ``Prop`` but ``bf`` is
computationally relevant. In other words, Coq gives you this warning:
|*)

Reset Initial. (* .none *)
Class btest : Prop := {
    bx : nat;
    bprop : bx = 0;
  }.
(* WARNING:
   bx cannot be defined because it is informative and btest is not.
   bprop cannot be defined because the projection bx was not defined.
*)
