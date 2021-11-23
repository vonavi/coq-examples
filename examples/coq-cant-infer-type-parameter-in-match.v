(*|
Coq can't infer type parameter in ``match``
===========================================

:Link: https://stackoverflow.com/questions/66881274/coq-cant-infer-type-parameter-in-match
|*)

(*|
Question
--------

Consider the following Coq program:
|*)

Inductive foo : nat -> Type :=
| nil : foo 0
| succ {n:nat} : foo n -> foo n.

(*| .. coq:: unfold fails |*)

Fail Fixpoint bar {n:nat} (A:foo n) (B:foo n) : Prop :=
  match B with
  | nil => False
  | succ C => bar A C
  end.

(*|
Coq complains on the definition of ``bar``.

But for ``B : foo n`` to be a ``succ C``, ``C`` must also be a ``foo
n``. Why can't Coq infer this, and how can I fix the definition of
``bar``?
|*)

(*|
Answer
------

When you match on ``B``, the type system "forgets" that the new ``n'``
inside ``B``'s type is the same as ``n``. There is a trick to add that
information to the context (there are many ways, plugins, etc. but it
is good to know how to do it "by hand"). It is called `"The convoy
pattern" by Adam Chlipala
<https://stackoverflow.com/search?q=convoy+coq>`_ and every coq user
must post a question about that once in his/her life (your's truly
included).

You make the body be not just a value but a function that takes an
additional input with the type ``n=n'`` and adds an ``eq_refl`` term
at the end. This plays well with how Coq's type system can break down
terms.

You can either rewrite the ``A`` type to change its type from ``foo
n`` to ``foo n'`` with tactics, like this:
|*)

Fixpoint bar (n:nat) (A:foo n) (B:foo n) : Prop.
  refine (
      match B in (foo m) return  (n=m -> _) with
      | nil => fun _ =>  False
      | @succ n' B' => fun (E : n = n') => bar n' _ B'
      end  eq_refl).
  rewrite E in A.
  apply A.
Defined.

(*| or directly with ``eq_rect`` |*)

Reset bar. (* .none *)
Fixpoint bar {n:nat} (A:foo n) (B:foo n) : Prop :=
  match B in (foo m) return  (n=m -> _) with
  | nil => fun _ =>  False
  | succ B' => fun E => bar (eq_rect _ _ A _ E) B'
  end eq_refl.
