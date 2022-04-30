(*|
######################################################
Matching expression context under ``forall`` with Ltac
######################################################

:Link: https://stackoverflow.com/q/45389615
|*)

(*|
Question
********

Say I have the following definitions in Coq:
|*)

Inductive Compare := Lt | Eq | Gt.

Fixpoint compare (x y : nat) : Compare :=
  match x, y with
  | 0, 0   => Eq
  | 0, S _ => Lt
  | S _, 0 => Gt
  | S x', S y' => compare x' y'
  end.

(*| Now consider this lemma: |*)

Lemma foo : forall (x : nat),
    (forall z, match compare x z with
               | Lt => False
               | Eq => False
               | Gt => False
               end) -> nat -> False.
Proof.
  intros x H y.

(*| At this point proof state looks like this: |*)

  Show. (* .unfold .messages *)

(*|
I'd like to write Ltac ``match goal`` that will detect that:

a) there is a hypothesis ``x : nat`` that is used as an argument to
   ``compare`` somewhere inside a quantified hypothesis ``H``
b) and there is some other hypothesis of type ``nat`` - namely ``y`` -
   that can be used to specialize the quantified hypothesis.
c) and once we have those two things specialize ``H`` to ``y``

I tried doing it like this:

.. code-block:: coq

    match goal with
    | [ X : nat, Y : nat, H : forall (z : nat), context[compare X z] |- _ ] =>
        specialize (H Y)
    end.

But there are at least two things that are wrong with this code:

1. Using ``context`` under a ``forall`` seems disallowed.
2. I can't figure out a correct way to pass ``X`` as argument to
   ``compare`` in a way that it is recognized as something that exists
   as a hypothesis.
|*)

(*|
Answer (Yves)
*************

If you want to check that ``X`` occurs in the quantified hypothesis
``H``, it suffices to check that it occurs in ``H`` after it is
instantiated with any value that does not contain ``X``. For instance,
you can instantiate ``H`` with ``Y`` by simply writing the application
of ``H`` as a function to ``Y``. Here is my proposal:
|*)

  match goal with
  | X : nat, H : _, Y : nat |- _ =>
      match type of (H Y) with
      | context[X] => specialize (H Y)
      end
  end.

(*|
This Ltac text really checks that ``H`` is a function. If you want to
be more precise and state that ``H`` should really be a universal
quantification (or a product type), then you can check that the type
of ``(H Y)`` also contains ``Y``, as in the following fragment:
|*)

  Undo. (* .none *)
  match goal with
  | X : nat, H : _, Y : nat |- _ =>
      match type of (H Y) with
      | context[X] =>
          match type of (H Y) with
          | context[Y] => specialize (H Y)
          end
      end
  end.

(*|
----

**Q:** Can you explain the meaning of ``match type``? Is this
documented anywhere in Coq manual?

**A:** Here you have the combination of two constructs of the Ltac
language. ``match ... with`` and ``type of``. If you write ``match H
with`` you only look at the symbol ``H``, on the other hand, if you
want to observe the hypothesis statement, you have to look at its
type. This is documented in section 9 of the manual.
|*)

(*|
Answer (Daniel Schoepe)
***********************

This doesn't quite do what you are asking for, but it's somewhat
close:
|*)

  Undo. (* .none *)
  match goal with
  | [ X : nat, Y : nat, H : context[compare ?a _] |- _ ] =>
      match type of H with
      | forall (z : nat), _ =>
          match a with
          | X => specialize (H Y)
          end
      end
  end.

(*|
However, this does not check that the second argument to ``compare``
matches the ``z`` that is bound by the ``forall``.
|*)
