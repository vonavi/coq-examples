(*|
#################################################
Coq - Obtaining equality from ``match`` statement
#################################################

:Link: https://stackoverflow.com/q/70946233
|*)

(*|
Question
********

Here's a simplified version of something I'm trying to implement in
Coq. I have an inductive type, say ``foo``, whose constructor takes in
another type ``A``, and a function with inputs in ``A``.
|*)

Inductive foo :=
| constructor (A : Type) (f : A -> bool).

(*|
I also have a function which, given an object of type ``foo``, tells
me what type was used to construct it.
|*)

Definition foo_type (x : foo) :=
  match x with
  | constructor A f => A
  end.

(*|
So far so good. But now, I want to define a function which takes in an
object ``x`` of type ``foo`` and an object ``y`` of type ``foo_type
x``, and returns the ``f y``, where ``f`` is the function used in the
constructor of ``x``.
|*)

Fail Definition foo_func (x : foo) (y : (foo_type x)) :=
  match x with
  | constructor A f => f y
  end. (* .fails *)

(*|
However, this doesn't work. Coq tells me that there is a type error:
``y`` is of type ``foo_type x``, when it should be of type ``A``.

Now, I know that ``foo_type x`` evaluates to ``A`` in this situation.
Using `this stackoverflow question
<https://stackoverflow.com/questions/52514957>`__, I found a function
I can use that takes as input an equality of types ``A = B`` and an
element ``a : A`` and returns ``a``, but of type ``B``. However, to
make use of this, I need to be able to obtain the equality ``foo_type
x = A`` within the ``match`` part of my function definition. This
boils down to obtaining the equality ``x = constructor A f``.

So: within a ``match x with`` statement in my definition, is it
possible to extract the equality ``x = constructor A f``? How can I do
this? Or is there another way to get around this issue?
|*)

(*|
Answer
******

You need to use dependent pattern matching (an give some information
to Coq) to get an equality proof between a term and its
pattern-matched content:

.. code-block:: coq

    match x as x0 return x = x0 -> ... with
    | pat => fun (e : x = pat) => ...
    | ...
    end eq_refl

On the outside of the match construct, you can build a term ``eq_refl
: x = x`` that is refined during pattern matching. This is called the
convoy pattern in `Certified programming with dependent types
<http://adam.chlipala.net/cpdt/>`__.

In your case however there is a related, slightly simpler alternative,
still using dependent pattern matching:
|*)

Definition foo_func (x : foo) (y : (foo_type x)) :=
  match x as x0 return foo_type x0 -> bool with
  | constructor A f => fun y => f y
  end y.

(*|
----

**A:** I would never write the first version, unless I was feeling the
need to write particularly bad code. Use the second version! (And you
would need about the same thing anyway, whether explicit or folded
into an existing lemma, to actually rewrite the equality you get from
the first version in the type of any term.)
|*)
