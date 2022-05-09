(*|
################################################
Pattern matching using information from theorems
################################################

:Link: https://stackoverflow.com/q/44413328
|*)

(*|
Question
********

I have the following question, look in the code.
|*)

(* Suppose we have type A *)
Variable A : Type.

(* Also we have a function that returns the type (option A) *)
Variable f_opt : A -> option A.

(* Then, I can prove that this function always returns something: *)
Theorem always_some : forall x, exists y, f_opt x = Some y.
Admitted.

(* Or, equivalently: *)
Theorem always_not_none : forall x, f_opt x <> None.
Admitted.

(*|
Now I would like to get a version of ``f_opt`` that always returns a
value of type ``A``. Something like this:
|*)

Fail Definition f x : A :=
  match f_opt x with
  | Some y => y
  end. (* .fails .unfold *)

(*|
I understand that I need to do some kind of work with types, but I do
not understand what exactly i should do.
|*)

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

In Coq's underlying theory, every pattern matching must be exhaustive
-- that is, it must explicitly consider all the constructors of the
inductive type in question. This is why you are getting the error
message you saw.

How do we get around this restriction? There are a few solutions.
First, let's see how to convince Coq that the ``None`` branch can
never occur. For this, we will use your ``always_not_none`` theorem:
|*)

Definition f x : A :=
  match f_opt x as res return res <> None -> A with
  | Some y => fun _ => y
  | None => fun H => match H eq_refl with end
  end (always_not_none x).

(*|
This code might look strange at first sight, but it almost performs
the pattern match you want. To explain to Coq that the ``None`` case
never arises, it combines ``always_not_none`` with the fact that
``f_opt x = None`` on that branch to derive a contradiction. This is
the ``H eq_refl`` term on that branch. Then, the ``match`` on that
contradiction suffices to convince Coq that the branch is spurious. A
bit more formally, because ``False``, the contradictory proposition,
is defined without any constructors, when we match on a term of type
``False``, there are no branches to deal with, and the entire
expression can return any type that we want -- in this case, ``A``.

What is strange about this code is the type annotations on the match,
and that it returns a function instead of something of type ``A``
directly. This is done because of how dependent pattern match works in
Coq: whenever we want to make use of information that we obtain from
being in a particular branch of a match (here, that ``f_opt x`` is
equal to ``None`` in that branch), we must explicitly make the match
return a function -- what Adam Chlipala calls the `convoy pattern
<http://adam.chlipala.net/cpdt/html/MoreDep.html>`__. This is done so
that Coq knows where you plan to use that extra information and check
that it is done correctly. Here, we use that ``f_opt x`` is ``None``
to feed the hypothesis needed by ``always_not_none x`` to derive a
contradiction.

Although this will solve your problem, I would generally advise you
against doing it this way. For instance, if you know that your ``A``
type is inhabited by some element ``a : A``, then you can simply make
``f`` return ``a`` on that branch. This has the benefit of avoiding
mentioning proofs inside your functions, which often gets in the way
when simplifying and rewriting terms.
|*)

(*|
Answer (Daniel Schepler)
************************

Using Coq's ``Program`` module, you can write an exhaustive pattern
match, but annotate that some branches should be impossible to reach
and then later provide the proof that this is the case:
|*)

Reset f. (* .none *)
Require Import Program.

Program Definition f x : A :=
  match f_opt x with
  | Some a => a
  | None => !
  end.
Next Obligation.
  destruct (always_some x). congruence.
Qed.

(*|
(The ``Program`` module does a lot of the work behind the scenes that
in a complete explicit definition you would have to write using the
"convoy pattern". Do be aware, however, that sometimes ``Program``
tends to generate lots of dependencies on ``JMeq`` and the axiom
``JMeq_eq`` when dependent types are involved, even when it might not
be necessary.)

----

**A:** To check if ``f`` depends on any additional axioms one can use
``Print Assumptions f.`` command.
|*)

(*|
Answer (Vinz)
*************

You will need to put your existential proof ``always_not_none`` in
``Set`` or ``Type`` to do so:
|*)

Reset always_some. (* .none *)
Theorem always_some : forall x, {y : A & f_opt x = Some y}.
Admitted.

(*|
Then you can do the following (or use ``refine`` or ``Program``):
|*)

Definition f (x : A) : A :=
  let s := always_some x in let (x0, _) := s in x0.
