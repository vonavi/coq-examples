(*|
######################################################
Proving ``False`` with negative inductive types in Coq
######################################################

:Link: https://stackoverflow.com/q/31226427
|*)

(*|
Question
********

The third chapter of CPDT briefly discusses why negative inductive
types are forbidden in Coq. If we had
|*)

Fail Inductive term : Set :=
| App : term -> term -> term
| Abs : (term -> term) -> term. (* .fails *)

(*|
then we could easily define a function

.. code-block:: coq

    Definition uhoh (t : term) : term :=
      match t with
      | Abs f => f t
      | _ => t
      end.

so that the term ``uhoh (Abs uhoh)`` would be non-terminating, with
which "we would be able to prove every theorem".

I understand the non-termination part, but I don't get how we can
prove anything with it. How would one prove ``False`` using ``term``
as defined above?
|*)

(*|
Answer
******

Reading your question made me realize that I didn't quite understand
Adam's argument either. But inconsistency in this case results quite
easily from Cantor's usual `diagonal argument
<https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument>`__ (a
never-ending source of paradoxes and puzzles in logic). Consider the
following assumptions:
|*)

Section Diag.

  Variable T : Type.
  Variable test : T -> bool.
  Variables x y : T.

  Hypothesis xT : test x = true.
  Hypothesis yF : test y = false.

  Variable g : (T -> T) -> T.
  Variable g_inv : T -> (T -> T).

  Hypothesis gK : forall f, g_inv (g f) = f.

  Definition kaboom (t : T) : T :=
    if test (g_inv t t) then y else x.

  Lemma kaboom1 : forall t, kaboom t <> g_inv t t.
  Proof using T test x y xT yF g_inv.
    intros t H.
    unfold kaboom in H.
    destruct (test (g_inv t t)) eqn:E; congruence.
  Qed.

  Lemma kaboom2 : False.
  Proof using T test x y xT yF g g_inv gK.
    assert (H := @kaboom1 (g kaboom)).
    rewrite -> gK in H.
    congruence.
  Qed.

End Diag.

(*|
This is a generic development that could be instantiated with the
``term`` type defined in CPDT: ``T`` would be ``term``, ``x`` and
``y`` would be two elements of ``term`` that we can test discriminate
between (e.g. ``App (Abs id) (Abs id)`` and ``Abs id``). The key point
is the last assumption: we assume that we have an invertible function
``g : (T -> T) -> T`` which, in your example, would be ``Abs``. Using
that function, we play the usual diagonalization trick: we define a
function ``kaboom`` that is by construction different from every
function ``T -> T``, including itself. The contradiction results from
that.
|*)
