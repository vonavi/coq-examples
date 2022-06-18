(*|
###########################################################################
Using length of list ``X`` as an argument for a constructor of ``X`` in Coq
###########################################################################

:Link: https://stackoverflow.com/q/26835278
|*)

(*|
Question
********

The title is not very informative, so let me explain.

I'm trying to formalize what it means to be a term in first-order
logic. Here is the textbook definition of terms of an arbitrary
language ``L``:

    1. Each variable or constant is a term.
    2. If ``n >= 1``, ``f`` is an ``n``-ary function of ``L``, and
       ``t1 ... tn`` are terms of ``L``, then ``f t1 ... tn`` is a
       term of ``L``.

I have already defined variables, constants, functions, and languages
as ``var``, ``const``, ``func``, and ``lang``. I also have functions
``f_arity`` and ``L_funcs`` that returns the arity of a function and
the ensemble of all functions in a language, respectively. So giving
an inductive definition of terms should be pretty straightforward:

.. coq:: none
|*)

Require Import List.
Import ListNotations.

Variable lang : Type.
Variables var const func : Type.
Variable f_arity : func -> nat.
Variable L_funcs : lang -> list func.
Variable listN : Type -> nat -> Type.

(*||*)

Fail Inductive term (L : lang) : Type :=
| t_v : var -> term L
| t_c : const -> term L
| t_f : forall (f : func) (l : list (term L)),
    length l = f_arity f ->
    In f (L_funcs L) -> term L. (* .fails *)

(*| But it doesn't work. Instead, I get this error message. |*)

Fail Inductive term (L : lang) : Type :=
| t_v : var -> term L
| t_c : const -> term L
| t_f : forall (f : func) (l : list (term L)),
    length l = f_arity f ->
    In f (L_funcs L) -> term L. (* .unfold .messages *)

(*|
I have a vague idea of what's going on here. The constructor ``t_f``
has an argument ``length l = f_arity``, which Coq doesn't like because
it has ``term L`` on the left side of an arrow. But I think Coq is
being overly cautious here, because it lets me do pretty much the same
thing if I tweak the types a bit. I could, for instance, define a
custom list type ``listN`` indexed by its size, so that ``list X n``
would be a list of ``X`` with ``n`` elements. Then I would have
|*)

Fail Inductive term (L : lang) : Type :=
| t_v : var -> term L
| t_c : const -> term L
| t_f : forall (f : func) (l : listN (term L) (f_arity f)),
    In f (L_funcs L) -> term L. (* .fails *)

(*|
But I don't want to go this way, because it is ad-hoc, and makes all
the useful list libraries unusable. So I'm looking for a way to
convince Coq that what I'm trying to do is perfectly safe, so it will
accept ``length l = f_arity f`` as a constructor argument. Is there a
way to do this?
|*)

(*|
Answer
******

This is a nice problem indeed, I hadn't encountered it in this form
before.

Quite frankly, unfortunately, I don't see a way of getting Coq to
accept your definition as is. Here are some options for mitigating
this problem:

1. Use a separate inductive predicate for term well-formedness.
   Manipulating terms will be much more convenient, because you won't
   have to worry about the length constraints when writing your
   functions. On the other hand, you will have to reason about
   well-formedness separately when proving anything about it. Thus,
   you would have something like
|*)

Inductive term (L : lang) :=
| t_v : var -> term L
| t_c : const -> term L
| t_f (f : func) (ts : list (term L)) : term L.

Inductive wf_term (L : lang) : term L -> Prop :=
| wf_v v : wf_term L (t_v L v)
| wf_c c : wf_term L (t_c L c)
| wf_f f ts :
  In f (L_funcs L) -> Forall (wf_term L) ts ->
  length ts = f_arity f -> wf_term L (t_f L f ts).

(*|
2. Use a dependently typed encoding for term. You can add e.g. a
   ``nat`` parameter to ``term`` for expressing how many arguments are
   "missing", which would give you something like
|*)

Reset term. (* .none *)
Inductive term L : nat -> Type :=
| t_v : var -> term L 0
| t_c : const -> term L 0
| t_f f : In f (L_funcs L) -> term L (f_arity f)
| t_a n (t : term L (S n)) (t : term L 0) : term L n.

(*|
   This might not be what you want, since you don't get the list of
   arguments to manipulate, but it might be helpful.

3. Use a "bad" encoding with a length-indexed list, and use auxiliary
   types ("views") and functions to make this "bad" definition more
   convenient to use. You define ``term`` like in your second
   definition, but then define a new ``term'`` on top of it, like
|*)

Reset term. (* .none *)
Variable term : lang -> Type. (* .none *)
Inductive term' L : Type :=
| t_v' : var -> term' L
| t_c' : const -> term' L
| t_f' f (ts : list (term L)) :
  In f (L_funcs L) -> length ts = f_arity f -> term' L.

Definition term_view L (t : term L) : term' L. (* ... *) Admitted.

(* Wrapper around the original constructor *)
Definition t_f'' L f ts :
  In f (L_funcs L) -> @length lang ts = f_arity f -> term L.
  (* ... *)
Admitted.

(*|
You can even define custom induction/recursion principles that work
directly with ``t_f''`` instead of ``t_f``, effectively hiding the
annoying details of your original definition.
|*)
