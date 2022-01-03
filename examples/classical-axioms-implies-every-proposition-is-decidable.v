(*|
########################################################
Classical axioms implies every proposition is decidable?
########################################################

:Link: https://stackoverflow.com/q/61316612
|*)

(*|
Question
********

In the Lean manual 'Theorem proving in Lean' I read: "With the
classical axioms, we can prove that every proposition is decidable".

I would like to seek clarification about this statement and I am
asking a Coq forum, as the question applies as much to Coq as it does
to Lean (but feeling I am more likely to get an answer here).

When reading "With the classical axioms", I understand that we have
something equivalent to the law of excluded middle:
|*)

Axiom LEM : forall (p : Prop), p \/ ~p.

(*|
When reading "every proposition is decidable", I understand that we
can define a function (or at least we can prove the existence of such
a function):
|*)

Inductive Dec (p : Prop) : Type :=
| isFalse : ~p -> Dec p
| isTrue  :  p -> Dec p.

Definition decide (p : Prop) : Dec p.

(*|
Yet, with what I know of Coq, I cannot implement ``decide`` as I
cannot destruct ``(LEM p)`` (of sort ``Prop``) to return something
other than a ``Prop``.

So my question is: assuming there is no mistake and the statement
"With the classical axioms, we can prove that every proposition is
decidable" is justified, I would like to know how I should understand
it so I get out of the paradox I have highlighted. Is it maybe that we
can prove the existence of the function ``decide`` (using ``LEM``) but
cannot actually provide a witness of this existence?
|*)

(*|
Answer
******

In the calculus of constructions without any axioms, there is
*meta-theoretical* property that every proof of ``A \/ B`` is
necessarily a proof that ``A`` holds (packaged using the constructor
``or_introl``) or a proof that ``B`` holds (using the other
constructor). So a proof of ``A \/ ~ A`` is either a proof that ``A``
holds or a proof that ``~ A`` holds.

Following this meta-theoretical property, in **Coq without any
axioms**, all proofs of propositions of the form ``forall x, P x \/ ~P
x`` actually are proofs that ``P`` is decidable. In this paragraph,
the meaning of ``decidable`` is the commonly accepted meaning, as used
by computability books.

Some users started using the word ``decidable`` for any predicate
``P`` so that there exists a proof of ``forall x, P x \/ ~ P x``. But
they are actually talking about a different thing. To make it clearer,
I will call this notion ``abuse-of-terminology-decidable``.

Now, if you add an axiom like LEM in Coq, you basically state that
every predicate ``P`` becomes ``abuse-of-terminology-decidable``. Of
course, you cannot change the meaning of ``conventionally-decidable``
by just adding an axiom in you Coq development, so there is no
inclusion anymore.

I have been fighting against this abuse of terminology for years, but
without success.

To be more precise, in Coq terminology, the term decidable is not used
for propositions or predicates that enjoy LEM, but for propositions or
predicates that enjoy the stronger following statement:

.. code-block:: coq

    forall x, {P x} + {~P x}

Proofs of such propositions are often named with ``_dec`` suffix,
where ``_dec`` directly refers to *decidable*. This abuse is less
strong, but it is still an abuse of terminology.

----

**Q:** Do you mean external vs internal decidability in the
terminology of nLab? ncatlab.org/nlab/show/decidable+proposition
(sect. 1)

**A:** Thanks for the pointer @AntonTrunov. No, I think there is an
extra difference between "externally decidable" and "decidable in the
common sense". In the article you point to, "externally decidable" is
a notion that is relative to a given theory. But when we say that the
halting problem is undecidable, we use the word "undecidable" in a
sense that is stronger and refers to the existence of an algorithm
taking inputs (programs in the case of the halting problem),
terminating for all inputs, deciding for each input whether the
property (the program halts) holds or not.
|*)
