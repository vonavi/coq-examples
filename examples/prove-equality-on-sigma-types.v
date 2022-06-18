(*|
#############################
Prove equality on Sigma-types
#############################

:Link: https://stackoverflow.com/q/27079513
|*)

(*|
Question
********

I have defined a Sygma-Type that looks like:

.. code-block:: coq

    { R : nat -> nat -> bool | Reflexive R }

I have two elements ``r1 r2 : { R : nat -> nat -> bool | Reflexive R
}`` and I am to prove ``r1 = r2``. How can I do that?
|*)

(*|
Answer
******

If you want to show such an equality, you need to (1) show that the
underlying functions are equal (i.e., the ``R`` component of your
sigma type), and (2) show that the corresponding proofs are equal.
There are two problems, however.

The first one is that equality of functions is too weak in Coq.
According to common mathematical practice, we expect two functions to
be equal if they yield equal results for any inputs. This principle is
known as *functional extensionality*:
|*)

Axiom functional_extensionality :
  forall A (B : A -> Type) (f g : forall a, B a),
    (forall x, f x = g x) -> f = g.

(*|
As natural as it sounds, however, this principle is not provable in
Coq's logic! Roughly speaking, the only way two functions can be equal
is if they can be converted to a syntactically equal terms according
to the computation rules of the logic. For instance, we can show that
``fun n : nat => 0 + n`` and ``fun n : nat => n`` are equal because
``+`` is defined in Coq by pattern-matching on the first argument, and
the first argument on the first term is ``0``.
|*)

Goal (fun n : nat => 0 + n) = (fun n : nat => n). reflexivity. Qed.

(*|
We could expect to show that ``fun n => n + 0`` and ``fun n => n`` are
equal by similar means. However, Coq does not accept this, because
``+`` cannot be simplified when the first argument is a variable.

The other problem is that the notion of equality on proofs is not very
interesting as well. The only way one can show that two proofs are
equal is, again, syntactic equality. Intuitively, however, one would
like to argue by *proof irrelevance*, a principle that states that
proofs of the same thing are always equal:
|*)

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

(*|
but, again, this principle is not provable in the logic. Fortunately,
Coq's logic was designed to allow one to add these principles as
axioms in a sound way. One then gets the following proof:
|*)

Reset Initial. (* .none *)
Axiom functional_extensionality :
  forall A (B : A -> Type) (f g : forall a, B a),
    (forall a, f a = g a) -> f = g.

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

Lemma l (r1 r2 : { R : nat -> nat -> bool | forall n, R n n = true }) :
  (forall n1 n2, proj1_sig r1 n1 n2 = proj1_sig r2 n1 n2) ->
  r1 = r2.
Proof.
  destruct r1 as [r1 H1], r2 as [r2 H2].
  simpl. intros H. assert (H' : r1 = r2).
  { apply functional_extensionality.
    intros n1.
    apply functional_extensionality.
    intros n2. apply H. }
  { subst r2. rename r1 into r. f_equal.
    apply proof_irrelevance. }
Qed.

(*|
Even though axioms can be useful, one might like to avoid them. In
this case, it is actually possible to prove this lemma just with
functional extensionality, but you do need at least that. If you want
to avoid using axioms, and ``r1`` and ``r2`` are *not* equal up to
computation, you'll have to use a difference equivalence relation on
your type, and do your formalization using that relation instead, e.g.
|*)

Definition rel_equiv
           (r1 r2 : { R : nat -> nat -> bool | forall n, R n n = true }) : Prop
  := forall n1 n2, proj1_sig r1 n1 n2 = proj1_sig r2 n1 n2.

(*|
The `standard library <http://coq.inria.fr/>`__ has good support for
rewriting with equivalence relations; cf. for instance `this
<https://coq.inria.fr/distrib/current/stdlib/Coq.Classes.SetoidClass.html>`__.

----

**A:** I wouldn't say, e.g., ``(fun x : nat => x)`` and ``(fun f => f)
(fun x : nat => x)`` are *syntactically* equal, but in Coq they are
equal. Perhaps it'd be better to replace "syntactically" with
"definitionally" or "up to computation"?

**A:** The ``l`` lemma can also be proved using the unicity of
equality proofs (UIP) axiom, which is *weaker* than the proof
irrelevance axiom. The modification is simple: we need to introduce
|*)

Axiom UIP : forall A (x y : A) (p1 p2 : x = y), p1 = p2.

(*|
and change ``apply proof_irrelevance.`` at the end of the proof into
``apply functional_extensionality; intros; apply UIP.``

**A:** On the first reading I missed your comment on the possibility
of proving this special case without proof irrelevance (or UIP). Since
``bool`` is a type with decidable equality, we can use
``UIP_refl_bool`` from ``Eqdep_dec`` module to finish the proof:
``apply functional_extensionality; intro. destruct (H2 _). apply
UIP_refl_bool.``
|*)
