(*|
############################################################
Proofs of structural properties of arguments in match in coq
############################################################

:Link: https://stackoverflow.com/questions/66064683/proofs-of-structural-properties-of-arguments-in-match-in-coq
|*)

(*|
Question
********

I would like to write a safe zip function in coq that accepts the
argument length equality as an argument.

.. coq:: fails
|*)

Fail Fixpoint zip {b a:Type} (l1 : list a) (l2 : list b)
     (proof : length l1 = length l2) : list (a * b) :=
  match l1,l2 with
  | nil, nil => nil
  | cons a a', cons b b' => cons (a, b) (zip a' b')
  | _, _ => _ (* never reached *)
  end.

(*|
what is the general approach to this kind of problem? I would
appreciate comments and resources on using refinement types in the
context of coq functions generally.
|*)

(*|
Answer
******

Here is the best approach to this particular problem, in my opinion:
|*)

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint zip_pre {A B} (xs : list A) (ys : list B) : list (A * B) :=
  match xs, ys with
  | x :: xs, y :: ys => (x, y) :: zip_pre xs ys
  | _, _ => []
  end.

Definition zip {A B} (xs : list A) (ys : list B) (_ : length xs = length ys) :=
  zip_pre xs ys.

(*|
In words, we first define a version of ``zip`` that does not care
about lengths, and then we use that to define the function you're
looking for.

This might feel like cheating; after all, the ``zip`` function doesn't
even use its proof argument! Here is another version that is perhaps
closer to what you were originally looking for:
|*)

Fixpoint zip' {A B} (xs : list A) (ys : list B) :
  length xs = length ys -> list (A * B) :=
  match xs, ys with
  | x :: xs, y :: ys =>
    fun H : S (length xs) = S (length ys) =>
      (x, y) :: zip' xs ys ltac:(congruence)
  | [], [] => fun _ => []
  | x :: xs, [] => fun H : S (length xs) = 0 => ltac:(easy)
  | [], y :: ys => fun H : 0 = S (length ys) => ltac:(easy)
  end.

(*|
Unlike ``zip``, ``zip'`` uses its proof argument in two ways. In the
contradictory cases, it invokes some tactic code (``ltac:(easy)``) to
argue that this case cannot arise. In the recursive case, it needs to
find a proof of ``length xs = length ys`` to apply the recursive call;
for this, it uses the ``congruence`` tacitc.

Why is ``zip`` better than ``zip'``? Its code is shorter and easier to
read. In particular, note how ``zip'`` has a match returning a
function. This idiom, known as the *convoy pattern*, is needed
whenever we need to refine the type of an argument in a pattern
matching branch. Actually, ``zip'`` is even worse than what you might
think, because the tactics that discharge the proof obligations
generate code. Try printing ``zip'`` to see what the definition really
looks like! Sadly, this ugliness is not just cosmetic: these more
complicated definitions are much harder to reason about. For instance,
it is possible to prove that ``zip`` and ``zip'`` always produce the
same outputs. Try it to see how fun it is!

To be fair, there are Coq plugins that make it easier to write this
sort of code (e.g. the `Equations
<https://github.com/mattam82/Coq-Equations>`__ plugin). But at the end
of the day they will still generate code that is equivalent to
``zip'``. And in this case, the length hypothesis doesn't buy us much.

In general, one is better off avoiding dependent types in Coq, unless
there is a strong argument that justifies the additional complexity.
For instance, in the case of ``zip``, suppose that you have some code
that uses a lot of different lists of the same length n. You might
want to argue that ``zip`` has an inverse:

.. code-block:: coq

    let xys := zip xs ys in
    (map fst xys, map snd xys) = (xs, ys).

It is not possible to prove this result unless we know that ``xs`` and
``ys`` have the same length. We can add an additional hypothesis to
our lemma, or we can work with length-indexed lists. Here is one
possible definition:
|*)

Definition vec A n := {l : list A | length l = n}.

(*|
The ``{.. | ..}`` is Coq's notation for refinement, or subset types.
We can then repackage some of the functions over lists to work over
``vec``. For instance, we can show that ``map`` takes ``vec A n`` to
``vec B n``. This approach pays off if you don't use many functions
that require you to change the length index ``n``, because in those
cases you need to reason about the equality of complicated length
expressions on types, which Coq is not very good at. For ``vec`` in
particular, I would recommend you to have a look at the ``tuple``
library of mathcomp (available `here
<https://math-comp.github.io/htmldoc/mathcomp.ssreflect.tuple.html>`__),
which provides a good example of how this pattern can be used at
scale.

**Edit**

- More on the ``easy`` tactic:
  https://coq.inria.fr/refman/proofs/automatic-tactics/auto.html#coq:tacn.easy
- Calling tactic code to build terms:
  https://coq.github.io/doc/V8.11.1/refman/language/gallina-extensions.html#solving-existential-variables-using-tactics
|*)
