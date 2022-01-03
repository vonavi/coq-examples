(*|
##############################
Show theorem definition in Coq
##############################

:Link: https://stackoverflow.com/q/62939436
|*)

(*|
Question
********

I'd like to view the definition of a Standard Library theorem which I
found through ``Search``. I think seeing the definition will help me
complete a similar theorem.

Doing ``Print Rdiv_lt_0_compat.`` yields:
|*)

Require Import Reals. (* .none *)
Print Rdiv_lt_0_compat. (* .unfold .messages *)

(*|
Setting ``Set Printing All.`` doesn't help. There's nothing extra
available in `the docs page
<https://coq.inria.fr/library/Coq.Reals.RIneq.html#Rdiv_lt_0_compat>`__.
|*)

(*|
Answer
******

The whole Coq system is based on the idea *Proofs are programs,
logical formulas are types*. When you consider a theorem, it is a
proof (a program) and its statement is a logical formula (the type of
a program). In the very first years of Coq, there was no tactic
language, every proof was defined using the same keywords as when
defining a program.

After a few years, it was recognized that writing the programs
entirely by hand was long and tiresome, so a tactic language was
invented to explain how to construct the *proof-programs* in a shorter
and less difficult way. But what is recorded and eventually checked
are still the programs that you see using ``Print``.

When building a proof-program, the tactic ``intros`` constructs
anonymous function expressions (also known as lambdas, usually written
with the keyword ``fun``, and ``apply`` constructs an application of a
function to a certain number arguments, which ``apply`` infers or
leaves to the user as goals. The tactics ``induction`` and ``rewrite``
are similar, but they apply theorems that are not given by the user.
The tactic ``destruct`` essentially produces a piece of programs that
is a pattern-matching construct.

With ``Rdiv_lt_0_compat``, you are lucky that the proof built by the
tactic is quite short. Often, proofs written using tactics produce
programs that are much longer.

If instead of the program, you want to see the sequence of tactics
that generated it, you need to find it in the sources of the system,
because this is not kept in the memory of the proof assistant. Here
are the clues.
|*)

Require Import Reals.

Locate Rdiv_lt_0_compat. (* .unfold *)

(*|
This sequence of names indicates the hierarchy of modules in which the
theorem is kept. The first name ``Coq`` expresses that this theorem is
in the Coq sources, essentially in directory ``...theories/``, the
second name ``Reals``, indicates that you should look in tge sub
directory ``...theories/Reals``. The fourth name should not be used as
a directory name, but as file name. So you should look in the file
``RIneq.v``

So go an look in
https://github.com/coq/coq/tree/v8.12/theories/Reals/RIneq.v and you
will probably find the script fragment that was used to generate your
theorem (for the 8.12 version of Coq). I just checked, the theorem
appears at line
https://github.com/coq/coq/blob/c95bd4cf015a3084a8bddf6d3640458c9c25b455/theories/Reals/RIneq.v#L2106

The sequence of names provided by ``Locate`` is not a sure way to find
the file where the script for a theorem is stored. The correspondence
between the long name and the file path is broken when the theorem is
defined using modules and functor instantiation. In that case, you
have to rely on stronger knowledge of how the Coq system works.
|*)
