(*|
####################################
Equality in Coq for enumerated types
####################################

:Link: https://stackoverflow.com/q/33708965
|*)

(*|
Question
********

I have a finite enumerated type (say ``T``) in Coq and want to check
elements for equality. This means, I need a function

.. code-block:: coq

    beq_T (x : T) (y : T) : bool

The only way I managed to define such a function, is with a case by
case analysis. This results in lots of match statements and looks very
cumbersome. Therefore, I wonder if there is not a simpler way to
achieve this.
|*)

(*|
Answer (eponier)
****************

Even simpler: ``Scheme Equality for ...`` generates two functions
returning respectively a boolean and a sumbool.
|*)

(*|
Answer (Konstantin Weitz)
*************************

The bad news is that the program that implements ``beq_T`` must
necessarily consist of a large match statement on both of its
arguments. The good news is that you can automatically
generate/synthesize this program using Coq's *tactic language*. For
example, given the type:
|*)

Inductive T := t0 | t1 | t2 | t3.

(*|
You can define ``beq_T`` as follows. The first two ``destruct``
tactics synthesize the code necessary to match on both ``x`` and
``y``. The ``match`` tactic inspects the branch of the match that it
is in, and depending on whether ``x = y``, the tactic either
synthesises the program that returns ``true`` or ``false``.
|*)

Definition beq_T (x y : T) : bool.
  destruct x, y;
    match goal with
    | _ : x = ?T, _ : y = ?T |- _ => exact true
    | _ => exact false
    end.
Defined.

(*| If you want to see the synthesized program, run: |*)

Print beq_T. (* .unfold *)

(*|
Thankfully, Coq already comes with a tactic that does almost what you
want. It is called ``decide equality``. It automatically synthesizes a
program that decides whether two elements of a type ``T`` are equal.
But instead of just returning a boolean value, the synthesized program
returns a proof of the (in)equality of the two elements.
|*)

Definition eqDec_T (x y : T) : {x = y} + {x <> y}.
  decide equality.
Defined.

(*|
With that program synthesized, it is easy to implement ``beq_T``.
|*)

Definition beq_T' {x y : T} : bool := if eqDec_T x y then true else false.
