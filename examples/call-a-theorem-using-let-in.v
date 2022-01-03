(*|
###########################
Call a theorem using let-in
###########################

:Link: https://stackoverflow.com/q/48279204
|*)

(*|
Question
********

I have a function ``f`` returning a pair. Then I prove some results
about it. In my lemmas, my first attempt to get each component was
using ``let (x, y) := f z in``. But then, trying to use these lemmas
seems cumbersome. ``apply`` does not work directly, I have to add the
lemma in the hypothesis using ``pose proof`` or a variant of it and
destruct ``f z`` to be able to use it. Is there a way to use let-in
smoothly in lemmas ? Or is it discouraged because it is painful to
use?

To complete my question, here are the other attempts I made to write
lemmas about ``f``. I tried using ``fst (f z)`` and ``snd (f z)``
directly, but I also found it cumbersome. Finally, I started my lemmas
with ``forall x y, (x,y) = f z ->``.

Here is a concrete example.
|*)

Require Import List. Import ListNotations.

Fixpoint split {A} (l : list A) :=
  match l with
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: l => let (l1, l2) := split l in (a :: l1, b :: l2)
  end.

Lemma split_in : forall {A} (l : list A) x,
    let (l1, l2) := split l in In x l1 \/ In x l2 <-> In x l.
Admitted. (* .none *)

Lemma split_in2 : forall {A} (l : list A) x,
    In x (fst (split l)) \/ In x (snd (split l)) <-> In x l.
Admitted. (* .none *)

Lemma split_in3 : forall {A} (l : list A) x l1 l2,
    (l1, l2) = split l -> In x l1 \/ In x l2 <-> In x l.
Admitted. (* .none *)
Reset split. (* .none *)

(*|
Answer
******

You have found what I believe is the correct solution. ``let (l1, l2)
:= ... in ...`` will block reduction and break everything. Whether you
use ``split_in2`` or ``split_in3`` depends on what your starting point
is.

Note, however, that turning on ``Primitive Projections`` and
redefining ``prod`` as a primitive record will make it so that
``split_in`` and ``split_in2`` are actually the same theorem, because
``split l`` and ``(fst (split l), snd (split l))`` are judgmentally
equal. You can do this with
|*)

Set Primitive Projections.
Record prod {A B} := pair { fst : A ; snd : B }.
Arguments prod : clear implicits.
Arguments pair {A B}.
Add Printing Let prod.
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Hint Resolve pair : core.

(*|
----

**A:** Indeed, if you copy-paste the code redefining ``prod`` as a
primitive record above your code, then you can prove:

.. coq:: none
|*)

Fixpoint split {A} (l : list A) :=
  match l with
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: l => let (l1, l2) := split l in (a :: l1, b :: l2)
  end.

Lemma split_in : forall {A} (l : list A) x,
    let (l1, l2) := split l in In x l1 \/ In x l2 <-> In x l.
Admitted.

(*||*)

Lemma split_in2 : forall {A} (l : list A) x,
    In x (fst (split l)) \/ In x (snd (split l)) <-> In x l.
Proof.
  intros. apply split_in.
Qed.
