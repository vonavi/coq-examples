(*|
########################################
Syntax error with ``<`` in Coq notations
########################################

:Link: https://stackoverflow.com/q/42239138
|*)

(*|
Question
********

The following code:

.. code-block:: coq

    Reserved Notation "g || t |- x < y" (at level 10).

    Inductive SubtypeOf :
      GammaEnv -> ThetaEnv -> UnsafeType -> UnsafeType -> Set :=
    | SubRefl :
      forall (gamma : GammaEnv) (theta : ThetaEnv) (u : UnsafeType),
        gamma || theta |- u < u
    where "g || t |- x < y" := (SubtypeOf g t x y).

gives the following error:

    Syntax error: '<' expected after [constr:operconstr level 200] (in
    [constr:operconstr])

I get a similar error if I use ``<:`` in place of ``<``.

But this code works fine:

.. code-block:: coq

    Reserved Notation "g || t |- x << y" (at level 10).

    Inductive SubtypeOf :
      GammaEnv -> ThetaEnv -> UnsafeType -> UnsafeType -> Set :=
    | SubRefl :
      forall (gamma : GammaEnv) (theta : ThetaEnv) (u : UnsafeType),
        gamma || theta |- u << u
    where "g || t |- x << y" := (SubtypeOf g t x y).

Why? Is there a precedence setting that can be changed to allow ``<``
or ``<:`` in notation? Is there built-in syntax that I'm colliding
with, and need to watch for when defining notations?
|*)

(*|
Answer
******

Coq uses an LL1 parser to process notations. It also can output the
grammar. So, let's check what we are getting with the following
|*)

Reserved Notation "g || t |- x < y" (at level 10).

Print Grammar constr.
(*|
outputs:

.. code-block:: coq

    ...
    | "10" LEFTA
      [ SELF; "||"; term LEVEL "200"; "|-"; term LEVEL "200"; "<"; NEXT
    ...

Here,

- ``10`` is our precedence level;
- ``LEFTA`` means left associativity;
- ``200`` is the default precedence level for inner subexpressions.

Taking into account the fact that a lower level binds more tightly
than a higher level and the fact that the level of ``<`` is 70 (see
`Coq.Init.Notations
<https://coq.inria.fr/library/Coq.Init.Notations.html>`__), we can
deduce that Coq is trying to parse the ``x < y`` part as a
subexpression for ``x``, consuming the ``<`` token, hence the error
message.

To remedy the situation we can explicitly disallow parsing the third
parameter as the less-than expression by assigning ``x`` higher
precedence, i.e. a lower level.
|*)

Reset Initial. (* .none *)
Reserved Notation "g || t |- x < y" (at level 10, x at level 69).

Print Grammar constr.

(*|
.. code-block:: coq

    ...
    | "10" LEFTA
      [ SELF; "||"; term LEVEL "200"; "|-"; term LEVEL "69"; "<"; NEXT
    ...
|*)
