(*|
######################################
generalizing expressions under binders
######################################

:Link: https://stackoverflow.com/q/46458710
|*)

(*|
Question
********

I need to generalize expression under the binder. For example, I have
in my goal two expressions:

.. code-block:: coq

    (fun a b => g a b c)

and

.. code-block:: coq

    (fun a b => f (g a b c))

And I want to generalize ``g _ _ c`` part:

One way to do is to rewrite them first into:

.. code-block:: coq

    (fun a b => (fun x y =>  g x y c) a b)

and the second into:

.. code-block:: coq

    (fun a b =>
       f (
           (fun x y =>  g x y c) a b
    ))

And then, to generalize ``(fun x y, g x y c)`` as ``somefun`` with
type ``A -> A -> A``. This will turn my expressions into:

.. code-block:: coq

    (fun a b => somefun a b)

and

.. code-block:: coq

    (fun a b => f (somefun a b))

The difficulty here is that the expression I am trying to generalize
is under the binder. I could not find either a tactic or LTAC
expression to manipulate it. How can I do something like this?
|*)

(*|
Answer
******

There are two keys to this answer: the `change tactic
<https://coq.inria.fr/distrib/V8.6.1/refman/Reference-Manual010.html#hevea_tactic130>`__,
which replaces one term with a convertible one, and generalizing ``c``
so that you deal not with ``g _ _ c`` but ``fun z => g _ _ z``; this
second key allows you to deal with ``g`` rather than with ``g``
applied to its arguments. Here, I use the ``pose`` tactic to control
what function applications get β reduced:
|*)

Axiom A : Type.
Axiom f : A -> A.
Axiom g : A -> A -> A -> A.
Goal forall c, (fun a b => g a b c) = (fun a b => f (g a b c)).
Proof.
  intro c. pose (fun z x y => g x y z) as g'.
  change g with (fun x y z => g' z x y).
  cbv beta.
  generalize (g' c). intro somefun. clear g'.

(*|
Here is an alternate version that uses ``id`` (the identity function)
to block ``cbv beta``, rather than using ``pose``:
|*)

Reset Initial. (* .none *)
Axiom A : Type.
Axiom f : A -> A.
Axiom g : A -> A -> A -> A.
Goal forall c, (fun a b => g a b c) = (fun a b => f (g a b c)).
Proof.
  intro c.
  change g with (fun a' b' c' => (fun z => id (fun x y => g x y z)) c' a' b').
  cbv beta.
  generalize (id (fun x y : A => g x y c)). intro somefun.
