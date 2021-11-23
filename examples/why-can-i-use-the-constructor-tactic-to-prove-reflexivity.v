(*|
##########################################################
Why can I use the constructor tactic to prove reflexivity?
##########################################################

:Link: https://stackoverflow.com/questions/65959309/why-can-i-use-the-constructor-tactic-to-prove-reflexivity
|*)

(*|
Question
********

The constructor tactic allows you to discharge a goal which is an
inductive datatype by automatically applying constructors. However,
definitional equality is not an inductive product in Coq. Then why
does Coq accept this proof?
|*)

Example zeqz : 0 = 0. constructor.

(*|
Answer
******

The equality type in Coq is defined as follows
|*)

Inductive eq (A : Type) (x : A) : A -> Prop :=
  eq_refl : x = x :> A

where "x = y :> A" := (@eq A x y) : type_scope.

(*|
that is it has a single reflexivity constructor.

To prove that ``0 = 0`` you need to construct a term of this type. The
only way to do this is to invoke ``eq_refl``. However in order to
invoke ``eq_refl`` the type checker needs to know that ``0`` is
convertible to ``0`` (that is they are definitionally equal).

----

The type ``eq`` is a semantic notion of equality, whereas definitional
equality is a syntactic notion. **This means that the proof assistant
cannot distinguish between definitionally equal terms, but it can
distinguish between semantically equal terms.** So the constructor
``eq_refl`` can be seen as a guarantee that definitional (syntactic)
equality *subsumes* semantic equality.

It is fruitful to ask whether terms may be semantically equal without
being syntactically equal. Such examples may only be obtained through
an axiom. For example, by the definition of the recursor (``nat_rec``,
or more technically, ``nat_ind``) for the natural numbers, or by an
`extensionality
<https://coq.inria.fr/library/Coq.Logic.FunctionalExtensionality.html>`_
axiom.
|*)
