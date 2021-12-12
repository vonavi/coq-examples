(*|
##############################################################
Difference between ``sumbool`` and intuitionnistic disjunction
##############################################################

:Link: https://stackoverflow.com/questions/51288196/difference-between-sumbool-and-intuitionnistic-disjunction
|*)

(*|
Question
********

According to Coq's documentation

    ``sumbool`` is a boolean type equipped with the justification of
    their value

I thought that was already a property of the disjunction, in the
intuitionnistic (or constructive) logic that Coq implements.

For example, to prove an excluded middle ``p \/ ~p`` in Coq, you have
to do actual work, it is not a logical axiom. So a proof of ``p \/ q``
must either be a proof of ``p`` or a proof of ``q``.

Then why do we need ``sumbool p q``?

**EDIT**

By replacing the tactics by exact proofs, I got more specific error
messages. This one is fine:
|*)

Lemma sumbool_or : forall p q : Prop, sumbool p q -> p \/ q.
Proof.
  exact (fun (p q : Prop) (H : sumbool p  q) =>
           match H with
           | left p0 => or_introl p0
           | right q0 => or_intror q0
           end).
Qed.

(*| However this one tells me |*)

Lemma or_sumbool : forall p q : Prop, p \/ q -> sumbool p q.
Proof.
  Fail exact (fun (p q : Prop) (H : p \/ q) =>
                match H with
                | or_introl p0 => left p0
                | or_intror q0 => right q0
                end). (* .fails .unfold .no-goals *)

(*|
I'm a bit surprised. So a primitive like ``match`` depends on the sort
of thing we want to prove? It looks low-level lambda-calculus though.
|*)

(*|
Answer
******

The ``sumbool`` type lives in Coq's computationally relevant universe
``Type`` (or ``Set``). In particular, we can write programs using
functions that return elements of ``{P} + {Q}`` (for instance, the
standard library's ``Nat.eq_dec : forall n m : nat, {n = m} + {n <>
m}``, which tests whether two numbers are equal).

Logical disjunction, on the other hand, belongs to the computationally
irrelevant universe ``Prop``. We cannot perform case analysis on a
proof of type ``P \/ Q`` because Coq was designed to erase proofs when
a program is extracted, and such a case analysis might alter the
outcome of a computation. This makes it safe for us, for example, to
add the excluded middle axiom ``forall P : Prop, P \/ ~ P`` without
impacting the execution of extracted programs.

It would also be possible to add a strong form of the excluded middle
that lives in ``Type``: ``forall P : Prop, {P} + {~P}``; however, if
we use this axiom to write programs, we will not be able to execute
them.

----

**A:** Think of what is going to happen at runtime. When extracting a
program (i.e. erasing all the proofs since you don't need them at
runtime) all arguments of type ``or A B`` can be erased, i.e. those
cannot have any influence on program execution. Whereas it's not
possible to remove a term of type ``sumbool A B``, we can only hope
that the extractor would erase the proofs ``left`` and ``right``
constructors carry. Essentially ``sumbool`` should turn into a plain
simple ``bool`` type at runtime (that was a part of my answer I was
writing, but Arthur beat me to it :)).

**A:** Note that the resulting type is ``Prop`` for ``or`` and ``Set``
for ``sumbool``. This means you can use terms of ``sumbool`` type as
*data*, but terms of ``or`` type is for *specification* purposes only.
Which one to use depends on what you are trying to achieve.
``sumbool`` can be used inside the logical world, but ``or`` can't
affect computations. You can prove ``Lemma sumbool_to_or P Q : {P} +
{Q} -> P \/ Q.``, but not ``P \/ Q -> {P} + {Q}``.
|*)
