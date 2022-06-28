(*|
##########################################
Relation between types prod and sig in Coq
##########################################

:Link: https://stackoverflow.com/q/13868705
|*)

(*|
Question
********

In Coq the type prod (with one constructor ``pair``) corresponds to
cartesian product and the type ``sig`` (with one constructor
``exist``) to dependent sum but how is described the fact that the
cartesian product is a particular case of dependent sum? I wonder
there is a link between ``prod`` and ``sig``, for instance some
definitional equality but I don't find it explicitely in the reference
manual.
|*)

(*|
Answer (Ptival)
***************

As a matter of fact, the type ``prod`` is more akin to ``sigT`` than
``sig``:
|*)

Set Printing All. (* .none *)
Print prod. (* .unfold .messages *)
Print sig. (* .unfold .messages *)
Print sigT. (* .unfold .messages *)

(*|
From a meta-theoretic point of view, ``prod`` is just a special case
of ``sigT`` where your ``snd`` component does not depend on your
``fst`` component. That is, you could define:
|*)

Definition prod' A B := @sigT A (fun _ => B).

Definition pair' {A B : Type} : A -> B -> prod' A B := @existT A (fun _ => B).

Definition onetwo := pair' 1 2.

(*|
----

They can not be definitionally equal though, since they are different
types. You could show a bijection:
|*)

Definition from {A B : Type} (x : @sigT A (fun _ => B)) : prod A B.
Proof. destruct x as [a b]. auto. Defined.

Definition to {A B : Type} (x : prod A B) : @sigT A (fun _ => B).
Proof. destruct x as [a b]. econstructor; eauto. Defined.

Theorem fromto : forall {A B : Type} (x : prod A B), from (to x) = x.
Proof. intros. unfold from, to. now destruct x. Qed.

Theorem tofrom : forall {A B : Type} (x : @sigT A (fun _ => B)), to (from x) = x.
Proof. intros. unfold from, to. now destruct x. Qed.

(*|
Answer (Anthony)
****************

A product is the special case of a dependent sum precisely when the
dependent sum is isomorphic to the common product type.

Consider the traditional summation of a series whose terms do not
depend on the index: the summation of a series of ``n`` terms, all of
which are ``x``. Since ``x`` does not depend upon the index, usually
denoted ``i``, we simplify this to ``n * x``. Otherwise, we would have
``x_1 + x_2 + x_3 + ... + x_n``, where each ``x_i`` can be different.
This is one way of describing what you have with Coq's ``sigT``: a
type that is an indexed family of ``x``\ s, where the index is a
generalization of the differing data constructors typically associated
with variant types.
|*)
