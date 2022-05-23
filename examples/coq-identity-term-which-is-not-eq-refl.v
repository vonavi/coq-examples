(*|
##########################################
Coq identity term which is not ``eq_refl``
##########################################

:Link: https://stackoverflow.com/q/35157052
|*)

(*|
Question
********

I am still wondering what it means that a term of the equality type
``eq`` in Coq can be different from ``eq_refl``.

Is the following term an example for this?

.. code-block:: coq

    ((fun x:nat => eq_refl x) 2).

This term is syntactically different from ``eq_refl``, but
nevertheless it computes to ``eq_refl``.

Does there exist examples of terms which do not compute to
``eq_refl``?

P.S. Its not a homework question ;-)
|*)

(*|
Answer
******

As you point out, ``(fun x => eq_refl x) 2`` is *not* actually
different from ``eq_refl 2``, since both expressions compute to the
same thing.

Answering your second question is a bit delicate, because it can be
interpreted in many different ways. Here's one possibility (which I
think is the one you had in mind):

    Are there any type ``T`` and terms ``x y : T``, such that there is
    a proof ``e`` of ``@eq T x y`` in the empty context that does
    *not* compute to ``@eq_refl T z`` (where ``z : T`` is the result
    of computing ``x`` and ``y``)?

I believe that the answer to this question is no. It should be
possible to prove it formally by arguing that, since Coq's theory is
strongly normalizing, ``e`` must have a normal form ``e'``, and that
all normal forms that have type ``eq`` must be ``eq_refl``.

Note that, if drop the requirement that ``e`` is typed in the empty
context, this does not hold anymore. For instance, consider the proof
term of ``forall n, n + 0 = n``.
|*)

Fixpoint plus_n_0 n : n + 0 = n :=
  match n return n + 0 = n with
  | 0 => eq_refl 0
  | S n' => match plus_n_0 n' in _ = m return S (n' + 0) = S m with
            | eq_refl => eq_refl (S (n' + 0))
            end
  end.

(*|
In the successor branch, we use the ``match`` to produce a proof of
``S (n' + 0) = S n'`` which does *not* compute to ``eq_refl``. This
happens because the ``match`` cannot reduce the ``plus_n_0 n'`` term,
since it's a function applied to a variable. However, if we apply
``plus_n_0`` to any concrete natural number (say, ``1729``), the
resulting proof will compute to ``eq_refl 1729`` (try it!).

Another thing worth pointing out is that, when arguing that every
closed proof of equality computes to ``eq_refl``, we had to reason
*outside* of Coq's logic, appealing to a normalization argument that
we cannot phrase as a Coq proposition: note that, because Coq
identifies terms up to convertibility, there's no way of writing a
proposition ``P : nat -> Prop`` such that ``P n`` holds if and only if
``n`` is a Coq term in normal form.

Given this fact, you may wonder if there's anyway of establishing that
result *inside* Coq's logic; that is,

.. code-block:: coq

    forall T (x : T) (e : x = x), e = eq_refl x,

or, paraphrased in English, "every proof of equality is equal to
``eq_refl``". As it turns out, this statement is *independent* of
Coq's logic, which means that it cannot be proved nor disproved within
Coq itself.

It may seem at first that this contradicts what I said earlier. But
recall that we can always add new axioms to Coq's logic if they don't
contradict results that can be proved inside the logic. This means
that it is perfectly fine to assume that there exists *some* type
``T``, *some* term ``x : T``, and *some* proof ``e`` of ``x = x`` such
that ``e <> eq_refl x``. If we added this axiom, then the argument I
gave earlier would no longer apply, since there would be normal forms
of equality proofs that would be syntactically different from
``eq_refl`` (namely, ``e``).

The fact that we cannot establish this result inside Coq's logic (and
similar formal systems, such as Martin-Löf's type theory) is exactly
what enables homotopy type theory. HoTT postulates the existence of
the univalence axiom, which allows one to produce provably different
proofs of equality.

**Edit** It is important to remember that there are two notions of
equality in Coq: *definitional equality* (i.e., terms that are equal
by simplification) and *propositional equality* (i.e., terms that we
can relate by ``=``). Definitionally equal terms are interchangeable
for Coq, whereas propositionally equal terms must be exchanged with an
explicit rewriting step (or using the ``match`` statement, as seen
above).

I was a bit lax in the discussion above about the difference between
these two variants. There are cases where proofs of equality are
propositionally equal even if they aren't so definitionally. For
instance, consider the following alternate proof of reflexivity for
``nat``:
|*)

Fixpoint eq_refl_nat (n : nat) : n = n :=
  match n return n = n with
  | 0 => eq_refl 0
  | S n' => match eq_refl_nat n' in _ = m return S n' = S m with
            | eq_refl => eq_refl (S n')
            end
  end.

(*|
The term ``eq_refl_nat`` is *not* definitionally equal to ``eq_refl``:
we cannot obtain ``eq_refl`` from ``eq_refl_nat`` just by
simplification. However, both are *propositionally* equal: as it turns
out, for ``nat``, it is possible to show that ``forall n (e : n = n),
e = eq_refl``. (As I mentioned above, this cannot be shown for
arbitrary Coq types.)

----

**Q:** your function ``eq_refl_nat`` is an example for a function
which is propositionally equal to ``eq_refl`` but not definitionally
equal. Is my simpler function above, ``fun x:nat => eq_refl x``, of
the same kind?

**A:**
No, because that is definitionally equal to ``eq_refl``, although it relies on a feature that was added to Coq only recently: eta conversion. You can try to write
|*)

Check (eq_refl : (fun n : nat => eq_refl n) = @eq_refl nat).

(*|
which has the effect of testing whether two things are definitionally
equal.

**A:** Regarding "It should be possible to prove it formally by
arguing that, since Coq's theory is strongly normalizing," Coq's
theory may be strongly normalizing, but Coq's implementation is not.
Closing a proof of equality with ``Qed`` will have it not reducing to
``eq_refl``. You can also break subject reduction using coinductive
types, so I suspect you can use this to block equality reduction.
|*)
