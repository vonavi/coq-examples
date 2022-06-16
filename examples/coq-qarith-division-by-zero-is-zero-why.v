(*|
#########################################
Coq QArith division by zero is zero, why?
#########################################

:Link: https://stackoverflow.com/q/29282819
|*)

(*|
Question
********

I noticed that in Coq's definition of rationals the inverse of zero is
defined to zero. (Usually, division by zero is not
well-defined/legal/allowed.)
|*)

Require Import QArith.
Lemma inv_zero_is_zero: (/ 0) == 0.
Proof. unfold Qeq. reflexivity. Qed.

(*|
Why is it so?

Could it cause problems in calculations with rationals, or is it safe?
|*)

(*|
Answer
******

The short answer is: yes, it is absolutely safe.

When we say that division by zero is not well-defined, what we
actually mean is that zero doesn't have a multiplicative inverse. In
particular, we can't have a function that computes a multiplicative
inverse for zero. However, it is possible to write a function that
computes the multiplicative inverse for all other elements, and
returns some arbitrary value when such an inverse doesn't exists (e.g.
for zero). This is exactly what this function is doing.

Having this inverse operator be defined everywhere means that we'll be
able to define other functions that compute with it without having to
argue explicitly that its argument is different from zero, making it
more convenient to use. Indeed, imagine what a pain it would be if we
made this function return an ``option`` instead, failing when we pass
it zero: we would have to make our entire code monadic, making it
harder to understand and reason about. We would have a similar problem
if writing a function that requires a proof that its argument is
non-zero.

So, what's the catch? Well, when trying to prove anything about a
function that uses the inverse operator, we will have to add explicit
hypotheses saying that we're passing it an argument that is different
from zero, or argue that its argument can never be zero. The lemmas
about this function then get additional preconditions, e.g.
|*)

Check Qmult_inv_r. (* .unfold .messages *)

(*|
Many other libraries are structured like that, cf. for instance the
definition of the `field axioms
<http://ssr.msr-inria.inria.fr/~jenkins/current/Ssreflect.ssralg.html>`__
in the algebra library of MathComp.

There *are* some cases where we want to internalize the additional
preconditions required by certain functions as type-level constraints.
This is what we do for instance when we use *length-indexed vectors*
and a safe ``get`` function that can only be called on numbers that
are in bounds. So how do we decide which one to go for when designing
a library, i.e. whether to use a rich type with a lot of extra
information and prevent bogus calls to certain functions (as in the
length-indexed case) or to leave this information out and require it
as explicit lemmas (as in the multiplicative inverse case)? Well,
there's no definite answer here, and one really needs to analyze each
case individually and decide which alternative will be better for that
particular case.
|*)
