(*|
######################################################
How do you prove in Coq that ``(e: p = p) = eq_refl``?
######################################################

:Link: https://stackoverflow.com/questions/60665385/how-do-you-prove-in-coq-that-e-p-p-eq-refl
|*)

(*|
Question
********

I am trying to prove this:
|*)

Lemma eq_eq: forall (U: Type) (p: U) (eqv: p = p), eq_refl = eqv.
Abort. (* .none *)

(*|
But there just seems to be no way to do it. The problem is the type
``p = p`` being an equality on the same term, and then trying to match
its instance. If this were not the case, it is easy enough to prove
that a term of a type with a single constructor is equal to that
constructor.
|*)

Lemma eq_tt: forall (U: Type) (x: unit), tt = x.
Proof fun (U: Type) (x: unit) =>
        match x as x' return tt = x' with
          tt => eq_refl
        end.

(*| But when you try the same strategy on my problem, it fails. |*)

Lemma eq_eq: forall (U: Type) (p: U) (eqv: p = p), eq_refl = eqv.
  Fail Proof fun (U: Type) (p: U) (eqv: p = p) =>
               match eqv as e in _ = p' return eq_refl = e with
                 eq_refl => eq_refl
               end. (* .unfold .fails *)

(*|
The problem is that the ``return`` clause here translates internally
to a predicate function something like this:

.. code-block:: coq

    fun (p': U) (e: p = p') => eq_refl = e

which fails to typecheck because we have now lost the constraint
between the 2 terms in ``e``'s equality and ``eq_refl`` requires that
constraint.

Is there any way around this problem? Am I missing something?
|*)

(*|
Answer
******

Your proposed lemma is precisely the statement of `uniqueness of
identity proofs (UIP) <https://ncatlab.org/nlab/show/axiom+UIP>`_. It
was first proven that the negation of UIP is consistent in MLTT with
`Hofmann and Streicher's groupoid model
<https://www.tcs.ifi.lmu.de/mitarbeiter/martin-hofmann/pdfs/agroupoidinterpretationoftypetheroy.pdf>`_
(pdf link). In this model, types are interpreted as groupoids, where
the identity type ``x = y`` is the set of morphisms from ``x`` to
``y`` in the groupoid. In this model, there can be more than one
distinct ``e: x = y``.

More recently, `homotopy type theory
<https://ncatlab.org/nlab/show/homotopy+type+theory>`_ has embraced
this point of view. Rather than mere groupoids, types are interpreted
as ∞-groupoids, with not only the possibility of multiple equalities
between ``x`` and ``y``, but also possibly multiple identities between
identities ``p q: x = y``, etc.

Suffice to say, your lemma isn't provable without an extra axiom such
as UIP mentioned above or `Axiom K
<https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29>`_.
|*)
