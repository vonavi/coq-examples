(*|
###############################################
Understanding how pattern matching works in Coq
###############################################

:Link: https://stackoverflow.com/q/72930287
|*)

(*|
Question
********

I'm currently following the `Software Foundations
<https://softwarefoundations.cis.upenn.edu/>`__ book, I am currently
on the **Lists chapter**. However, I'm having a hard time wrapping my
head around a specific case of pattern matching and, due to being a
beginner in Coq, I'm not sure about how to find the answer of this
question.

So, the exercise was to create a ``Fixpoint`` to calculate how many
nat ``v`` we have in a list ``s`` (a bag, more specifically).

I decided to use pattern matching for this, but if I tried to define a
function like this:

.. coq:: none
|*)

Require Import List.
Import ListNotations.

Definition bag := list nat.

(*||*)

Fixpoint count' (v : nat) (s : bag) : nat :=
  match s with
  | nil => O
  | h :: t => match h with
              | v => S (count' v t)
              end
  end.

(*| and tried to apply this function to, let's say, |*)

Example test_count1 : count' 1 [1;2;3;1;4;1] = 3.

(*|
I would end up with ``6 = 3``. My understanding is that matching ``h``
with ``v`` is always "true", so it ends up counting every element of
the list.

But why does it happen? How could we compare, using pattern matching,
the values of both ``h`` and ``v``?

**PS:** I have already solved this exercise using an auxiliary
function that compares if ``h`` and ``v`` are equal, but I'm wondering
if this can be achieved only using built-in pattern matching.
|*)

(*|
Answer (Li-yao Xia)
*******************

The pattern

.. code-block:: coq

    match h with
    | v => S (count' v t)
    end

introduces a new variable ``v`` bound to ``h``, shadowing the existing
``v``. It is equivalent to a ``let`` expression:

.. code-block:: coq

    let v := h in S (count' v t)
    (* or, without shadowing *)
    let v1 := h in S (count' v1 t)

Instead, to compare ``h`` and ``v``, use a comparison function:

.. code-block:: coq

    if h =? v then ... else ...
|*)

(*|
Answer (Ana Borges)
*******************

Pattern matching is useful when you want to make case distinctions on
constructors. Perhaps the name is misleading in this sense, since

.. code-block:: coq

    match h with
    | v => ...
    end

will not compare ``h`` and the specific ``v`` from above. Instead, the
``match`` checks to see if the shape of ``h`` matches the shape
exemplified by ``v``. Like Li-yao Xia mentioned, here ``v`` has no
shape, it is a universal placeholder. On the other hand something like

.. code-block:: coq

    match h with
    | O => ...
    | S k => ...
    end

exposes two different shapes that a ``nat`` can have, namely being
``O`` or the successor of some ``k``. The latter is the kind of
situation where we do want to use ``match``. Comparing values is best
done through ``_ =? _``.
|*)
