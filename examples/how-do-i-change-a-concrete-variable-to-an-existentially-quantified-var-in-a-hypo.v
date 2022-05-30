(*|
#######################################################################################
How do I change a concrete variable to an existentially quantified var in a hypothesis?
#######################################################################################

:Link: https://stackoverflow.com/q/32402952
|*)

(*|
Question
********

Say I have a hypothesis like this:

.. code-block:: coq

    FooProp a b

I want to change the hypothesis to this form:

.. code-block:: coq

    exists a, FooProp a b.

How can I do this?

I know I can do ``assert (exists a, FooProp a b) by eauto`` but I'm
trying to find a solution that doesn't require me to explicitly write
down the entire hypothesis; this is bad for automation and is just
generally a headache when the hypothesis are nontrivial. Ideally I'd
like to specify ``intro_exists a in H1`` or something; it really
should be that simple.

**EDIT**: Why? Because I have a lemma like this:

.. code-block:: coq

    Lemma find_instr_in : forall c i,
        In i c <-> (exists z : Z, find_instr z c = Some i).

And a hypothesis like this:

.. code-block:: coq

    H1: find_instr z c = Some i

And I'm trying to rewrite like this:

.. code-block:: coq

    rewrite <- find_instr_in in H1

Which fails with the error ``Found no subterm matching "exists z, ..."
...``. But if I ``assert (exists z, find_instr z c = Some i) by
eauto.`` first the rewrite works.
|*)

(*|
Answer
******

How about something like this:
|*)

Ltac intro_exists' a H :=
  pattern a in H; apply ex_intro in H.

Tactic Notation "intro_exists" ident(a) "in" ident(H) := intro_exists' a H.

Section daryl.
  Variable A B : Type.
  Variable FooProp : A -> B -> Prop.

  Goal forall a b, FooProp a b -> False.
    intros.
    intro_exists a in H.
  Admitted.
End daryl.

(*|
The key to this is the ``pattern`` tactic, which finds occurrences of
a term and abstracts them into a function applied to an argument. So
``pattern a`` converts the type of ``H`` from ``FooProp a b`` to
``(fun x => FooProp x b) a``. After that, Coq can figure out what you
mean when you apply ``ex_intro``.

----

**Edit:** All that being said, in your concrete case I would actually
recommend a different approach, which is to not state your lemma like
that. Instead it is convenient to split it into two lemmas, one for
each direction. The forwards direction is just the same, but the
backwards direction should be restated as follows

.. code-block:: coq

    forall c i z,
      find_instr z c = Some i -> In i c.

If you do this, then the rewrite will succeed without needing to
introduce the existential.
|*)
