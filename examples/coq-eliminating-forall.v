(*|
############################
Coq: eliminating ``forall``?
############################

:Link: https://stackoverflow.com/questions/68744549/coq-eliminating-forall
|*)

(*|
Question
********

I am struggling to prove the following theorem (non-empty domain is
assumed):
|*)

Theorem t (A: Set) (P: A -> Prop): (forall a: A, P a) -> (exists a: A, P a).
Proof.
  intros H.
Abort. (* .none *)

(*|
Normally, having ``forall a: A, P a`` I would deduce ``P c``, where
``c`` is a constant. I.e. ``forall`` quantifier would be eliminated.
Once that done I would again deduce ``exists a`` and my simple proof
will be ``Qed``'ed.

However, I can't find right way to eliminate on ``forall`` in Coq.

I am new to it and I'd like to know how to eliminate ``forall`` in Coq
or what's the better way to prove the above-mentioned theorem?

P.S. I have seen `this
<https://stackoverflow.com/questions/35994491/coq-elimination-of-forall-quantifier>`_
answer but it seems to be unrelated to my question.
|*)

(*|
Answer
******

Unlike other logical formalisms (e.g. Isabelle/HOL), in Coq it is
perfectly possible to have an empty domain. If you want to prove your
statement, you have to assume explicitly that ``A`` is not empty. Here
is one possibility.
|*)

Definition non_empty (A : Type) : Prop :=
  exists x : A, True.

Theorem t (A : Set) (P : A -> Prop) :
  non_empty A ->
  (forall a : A, P a) ->
  (exists a : A, P a).
Proof.
  intros [c _] H. exists c. apply H.
Qed.

(*|
----

**Q:** Thanks, is that precisely why ``False`` is defined as an empty
type which can not be constructed in any way?

**A:** Yes, it is related to that.
|*)
