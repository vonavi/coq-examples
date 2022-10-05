(*|
#########################################################
Why are logical connectives and booleans separate in Coq?
#########################################################

:Link: https://stackoverflow.com/q/31554453
|*)

(*|
Question
********

I come from a JavaScript/Ruby programming background and am used to
this being how true/false works (in JS):

.. code-block:: javascript

    !true
    // false
    !false
    // true

Then you can use those true/false values with ``&&`` like

.. code-block:: javascript

    var a = true, b = false;
    a && !b;

So *and* and *not* (and other logical/boolean operators) are part of a
single system; it seems like the "logical" system and the "boolean"
system are one and the same.

However, in Coq, logics and booleans are two separate things. Why is
this? The quote/link below demonstrates how a theorem is necessary to
relate them.

    We've already seen several places where analogous structures can
    be found in Coq's computational (``Type``) and logical (``Prop``)
    worlds. Here is one more: the boolean operators ``andb`` and
    ``orb`` are clearly analogs of the logical connectives ``/\`` and
    ``\/``. This analogy can be made more precise by the following
    theorems, which show how to translate knowledge about ``andb`` and
    ``orb``'s behaviors on certain inputs into propositional facts
    about those inputs.
|*)

Theorem andb_prop : forall b c,
    andb b c = true -> b = true /\ c = true.
Admitted. (* .none *)

(*|
http://www.seas.upenn.edu/~cis500/current/sf/Logic.html#lab211

----

**A (Vinz):** Short answer: not everything you can state in Coq is
provable (for example, take the halt problem. Could you prove it
(``True``) or refute it (``False``) or do you need a "gray" state for
this one ?). That's just a tiny part of the explanation, but it should
jump start your thoughts :)
|*)

(*|
Answer
******

*Essentially, Coq has both because they are useful for different
things: booleans correspond to facts that can be checked mechanically
(i.e., with an algorithm), whereas propositions can express more
concepts.*

Strictly speaking, the logical and boolean worlds are not separate in
Coq: the boolean world is a subset of the logical world. In other
words, every statement that you can phrase as a boolean computation
can be viewed as a logical proposition (i.e., something of type
``Prop``): if ``b : bool`` represents a statement, we can assert that
this statement is true by saying ``b = true``, which is of type
``Prop``.

The reason there's more in Coq to logic than just booleans is that the
converse of the previous statement does not hold: *not all logical
facts can be viewed as boolean computations*. Put in a different way,
it is not the case that booleans in normal programming languages such
as Ruby and JavaScript subsume both ``bool`` and ``Prop`` in Coq,
because ``Prop``\ s can express things that booleans in these
languages cannot.

To illustrate this, consider the following Coq predicate:
|*)

Definition commutative {T} (op : T -> T -> T) : Prop :=
  forall x y, op x y = op y x.

(*|
As the name suggests, this predicate asserts that an operator ``op``
is commutative. Many operators in programming languages are
commutative: take multiplication and addition over integers, for
instance. Indeed, in Coq we can prove the following statements (and I
believe those are examples in the Software Foundations book):
|*)

Lemma plus_comm : commutative plus. Proof. (* ... *) Admitted.
Lemma mult_comm : commutative mult. Proof. (* ... *) Admitted.

(*|
Now, try to think how you would translate a predicate like
``commutative`` in a more conventional language. If this seems
difficult, it is not by chance: it is possible to prove that we can't
write a program returning a boolean in these languages to test whether
an operation is commutative or not. You can certainly write *unit
tests* for checking whether this fact is true for particular inputs,
e.g.:

.. code-block:: coq

    2 + 3 == 3 + 2
    4 * 5 == 5 * 4

However, if your operator works with an infinite number of inputs,
these unit tests can only cover a fraction of all possible cases.
Therefore, testing is always necessarily weaker than a complete formal
proof.

You could wonder why we bother having booleans in Coq if ``Prop``\ s
can express everything that booleans can. The reason for that is that
Coq is a *constructive logic*, which is what Vinz was alluding to in
his comment. The most well-known consequence of this fact is that in
Coq we cannot prove the following intuitive principle:
|*)

Definition excluded_middle := forall P : Prop, P \/ ~ P.

(*|
which essentially says that every proposition is either true or false.
"How could this possibly fail?", you might ask yourself. Roughly
speaking, in constructive logics (and Coq in particular), every proof
corresponds to an algorithm we can execute. In particular, when you
prove a statement of the form ``A \/ B`` in a constructive logic, you
can extract an (always terminating) algorithm from that proof that
answers whether ``A`` or ``B`` holds. Hence, if we were able to prove
the above principle, we would have an algorithm that, given some
proposition, tells us whether that proposition is valid or not.
Computability theory shows, however, that this is not possible in
general because of undecidability: if we take ``P`` to mean "program
``p`` halts on input ``x``", the excluded middle would yield a decider
for the `halting problem
<https://en.wikipedia.org/wiki/Halting_problem>`__, which cannot
exist.

Now, what's interesting about booleans in Coq is that by construction
they allow the use of the excluded middle, because they *do*
correspond to an algorithm we can run. Specifically, we can prove the
following:
|*)

Lemma excluded_middle_bool :
  forall b : bool, b = true \/ negb b = true.
Proof. intros b. destruct b; auto. Qed.

(*|
Thus, in Coq it is useful to consider booleans as a special case of
propositions because they allow forms of reasoning that other
propositions do not, namely, case analysis.

Of course, you can think that requiring that every proof correspond to
an algorithm is silly, and indeed most logics allow the principle of
the excluded middle. Examples of proof assistants that follow this
approach by default include `Isabelle/HOL
<https://isabelle.in.tum.de/>`__ and the `Mizar <http://mizar.org/>`__
system. In these systems, we don't have to have a distinction between
booleans and propositions, and they are treated as the same thing.
Isabelle, for instance, has just ``bool``, and no ``Prop``. Coq also
allows you to blur the distinction between booleans and propostions,
by assuming axioms that allow you to perform case analysis on general
propositions. On the other hand, in such a setting, when you write a
function that returns a boolean, you might not obtain something that
you can execute as an algorithm, whereas this is always the case by
default in Coq.
|*)
