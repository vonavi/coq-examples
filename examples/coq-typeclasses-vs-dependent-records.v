(*|
#####################################
Coq: typeclasses vs dependent records
#####################################

:Link: https://stackoverflow.com/q/29872260
|*)

(*|
Question
********

I can't understand the difference between typeclasses and dependent
records in Coq. The reference manual gives the syntax of typeclasses,
but says nothing about what they really are and how should you use
them. A bit of thinking and searching reveals that typeclasses
essentially *are* dependent records with a bit of syntactic sugar that
allows Coq to automatically infer some implicit instances and
parameters. It seems that the algorithm for typeclasses works better
when there is more or a less only one possible instance of it in any
given context, but that's not a big issue since we can always move all
fields of typeclass to its parameters, removing ambiguity. Also the
``Instance`` declaration is automatically added to the Hints database
which can often ease the proofs but will also sometimes break them, if
the instances were too general and caused proof search loops or
explosions. Are there any other issues I should be aware of? What is
the heuristic for choosing between the two? E.g. would I lose anything
if I use only records and set their instances as implicit parameters
whenever possible?
|*)

(*|
Answer
******

You are right: type classes in Coq are just records with special
plumbing and inference (there's also the special case of single-method
type classes, but it doesn't really affect this answer in any way).
Therefore, the only reason you would choose type classes over "pure"
dependent records is to benefit from the special inference that you
get with them: inference with plain dependent records is not very
powerful and doesn't allow you to omit much information.

As an example, consider the following code, which defines a monoid
type class, instantiating it with natural numbers:
|*)

Class monoid A :=
  Monoid {
      op : A -> A -> A;
      id : A;
      opA : forall x y z, op x (op y z) = op (op x y) z;
      idL : forall x, op id x = x;
      idR : forall x, op x id = x
    }.

Require Import Arith.

Instance nat_plus_monoid : monoid nat :=
  {|
    op := plus;
    id := 0;
    opA := plus_assoc;
    idL := plus_O_n;
    idR := fun n => eq_sym (plus_n_O n)
  |}.

(*|
Using type class inference, we can use any definitions that work for
any monoid directly with ``nat``, without supplying the type class
argument, e.g.
|*)

Definition times_3 (n : nat) := op n (op n n).

(*|
However, if you make the above definition into a regular record by
replacing ``Class`` and ``Instance`` by ``Record`` and ``Definition``,
the same definition fails:

.. coq:: none
|*)

Reset Initial.

Record monoid A :=
  Monoid {
      op : A -> A -> A;
      id : A;
      opA : forall x y z, op x (op y z) = op (op x y) z;
      idL : forall x, op id x = x;
      idR : forall x, op x id = x
    }.

Require Import Arith.

Definition nat_plus_monoid : monoid nat :=
  {|
    op := plus;
    id := 0;
    opA := plus_assoc;
    idL := plus_O_n;
    idR := fun n => eq_sym (plus_n_O n)
  |}.

(*||*)

Fail Definition times_3 (n : nat) := op n (op n n). (* .unfold .messages *)

(*|
The only caveat with type classes is that the instance inference
engine gets a bit lost sometimes, causing hard-to-understand error
messages to appear. That being said, it's not really a disadvantage
over dependent records, given that this possibility isn't even
available there.
|*)
