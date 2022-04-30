(*|
#######################################
``Hint Rewrite`` cannot infer parameter
#######################################

:Link: https://stackoverflow.com/q/45425591
|*)

(*|
Question
********

I'm trying to create a Hint Rewrite database for a matrix library I've
written. However when I write

.. code-block:: coq

    Hint Rewrite kron_1_r : M_db.

I get the following error:

    Cannot infer the implicit parameter ``m`` of ``kron_1_r`` whose
    type is ``nat``.

``kron_1_r`` has the type ``forall {m n : nat} (A : Matrix m n), A ⊗
Id 1 = A``, so ``m`` and ``n`` should be inferred based on the context
when autorewrite is called. I'm not sure why it wants a parameter
here, or how to tell it to hold off.

----

**Q:** Replacing ``kron_1_r`` with ``@kron_1_r`` seems to solve the
problem, but the behavior still strikes me as pretty weird. (And in
context, it means that I have to put ``@`` signs everywhere.)

**A (Anton Trunov):** You are using maximally inserted implicit
arguments. This means Coq is trying to insert them even if you haven't
supplied any argument at all (right at the point you are trying to add
hints to the database). Try making them non-maximally inserted.

**Q:** Any suggestions on how to do that? I've tried ``Unset Maximal
Implicit Insertion`` without success. ``Arguments kron_1_r : clear
implicits`` works, but I don't want to clear implicits altogether.

**A (Anton Trunov):** Try something like ``Arguments kron_1_r [m n]
_.`` See the examples at the end of `sect. 2.7.4
<https://coq.inria.fr/refman/Reference-Manual004.html#sec112>`__.
|*)

(*|
Answer
******

You're running into the difference between *maximally inserted
implicit arguments* and normal implicit arguments. The difference is
exactly when you use a definition without giving any arguments, the
way you are in ``Hint Rewrite kron_1_r``. One solution is of course to
use ``@kron_1_r``, which gives the identifier without any implicit
arguments.

Unfortunately there's no syntax when creating a definition to give it
non-maximally inserted implicit arguments; you can only use ``{m :
nat}``. Instead, you'll need to use ``Arguments kron_1_r [m n] _.``
after creating ``kron_1_r`` to change the implicit behavior of the
first two arguments (as suggested by Anton Trunov above).

It's often helpful to use ``About``, which reports the status of
implicit arguments (you get these with ``Print`` as well, but you
usually get too much output when you print theorems since proof terms
are large).
|*)
