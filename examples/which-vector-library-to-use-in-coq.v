(*|
###################################
Which vector library to use in Coq?
###################################

:Link: https://stackoverflow.com/q/42302300
|*)

(*|
Question
********

I'm wondering, is there a commonly used library for vectors in Coq,
i.e. lists indexed by their length in their type.

Some tutorials reference ``Bvector``, but it's not found when I try to
import it.

There's ``Coq.Vectors.Vectordef``, but the type defined there is just
named ``t`` which makes me think it's intended for internal use.

What is the best or most common practice for someone who doesn't want
to roll their own library? Am I wrong about the vectors in the
standard library? Or is there another lib I'm missing? Or do people
just use lists, paired with proofs of their length?

----

**A:** I think @ejgallego answers this question in this `coq-club
thread
<https://sympa.inria.fr/sympa/arc/coq-club/2017-01/msg00099.html>`__.
Also, `this answer <http://stackoverflow.com/a/30159566/2747511>`__ by
Arthur Azevedo de Amorim has the same spirit: "While dependent types
are interesting for some things, it not clear how useful they are in
general. My impression is that some feel that they are very
complicated to use, and that the benefit of having certain properties
expressed at the type level versus having them as separate theorems is
not worth this additional complexity."

**A:** Also, you can ``Require Vector`` (without importing) and use
the qualified name ``Vector.t``.

**A:** If you want something ready to use AFAICT math-comp's ``tuple``
is the only option, others have experimented with "the fixpoint
definition", you may have luck with it too.
|*)

(*|
Answer
******

There are generally three approaches to vectors in Coq, each with
their own trade-offs:

1. Inductively defined vectors, as provided by the Coq standard
   library.
2. Lists paired with an assertion of their length.
3. Recursively-nested tuples.

Lists-with-length are nice in that they're easily coerced to lists, so
you can reuse a lot of functions that operate on plain lists.
Inductive vectors have the downside of requiring a lot of
dependently-typed pattern matching, depending on what you're doing
with them.

For most developments, I prefer the recursive tuple definition:
|*)

Definition Vec A : nat -> Type :=
  fix vec n := match n return Type with
               | O   => unit
               | S n => prod A (vec n)
               end.
