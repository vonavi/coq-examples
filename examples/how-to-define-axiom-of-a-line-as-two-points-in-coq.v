(*|
##################################################
How to define axiom of a line as two points in Coq
##################################################

:Link: https://stackoverflow.com/q/54937970
|*)

(*|
Question
********

I am trying to find an example *axiom* in `Coq
<https://github.com/GeoCoq/GeoCoq/blob/master/Axioms/euclidean_axioms.v>`__
of something like the line axiom in geometry: If given two points,
there exist a line between those two points. I would like to see how
this could be defined in Coq. Inherently choosing this simple line
axiom to see how something very primitive is defined, because I'm
having a hard time defining it outside natural language.

Specifically, I have seen these two axioms and would like to know how
in Coq to define both:

::

    1. Any two distinct points always determine a line
    2. Any two distinct points of a line determine this line uniquely

It almost seems like you can merge them into one definition, so I
would like to see syntactically and semantically how to write this in
Coq.

I don't know how to write Coq really, just looking to see how they do
it. But if I were to try it seems like this:

.. code-block:: coq

    Axiom line : forall ptA ptB : Point, line ptA ptB.

But that needs a Line and a Point object.

.. code-block:: coq

    Axiom line : forall ptA ptB, line ptA ptB.
    Definition Line ptA ptB -> (* (...) No idea. *)
    Definition Point ...
|*)

(*|
Answer
******

Here is a possibility. The ``exists!`` connective means unique
existence.
|*)

Axiom point : Type.
Axiom line : Type.
Axiom lies_in : point -> line -> Prop.
Axiom ax : forall (p1 p2 : point),
    p1 <> p2 -> exists! l : line, lies_in p1 l /\ lies_in p2 l.
