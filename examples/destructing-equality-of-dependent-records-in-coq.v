(*|
################################################
Destructing equality of dependent records in coq
################################################

:Link: https://stackoverflow.com/q/54569749
|*)

(*|
Question
********

Given a dependent record type:

.. code-block:: coq

    Record FinPath : Type := mkPath { fp_head : S i;
                                      fp_tail : FinPathTail fp_head
                                    }.

and two objects of type ``Path`` that are equal, I'd like to infer
that their heads and tails are equal. The problem is that I quickly
get something of this form:

.. code-block:: coq

    fpH : {| path_head := fp_head fp; path_tail := fpt_to_pt (fp_tail fp) |} =
          {| path_head := fp_head fp'; path_tail := fpt_to_pt (fp_tail fp') |}

Using the injection tactic, I can infer that ``fp_head fp = fp_head
fp'`` and also this term:

.. code-block:: coq

    existT (fun path_head : S i => PathTail path_head) (fp_head fp)
           (fpt_to_pt (fp_tail fp)) =
    existT (fun path_head : S i => PathTail path_head) (fp_head fp')
           (fpt_to_pt (fp_tail fp'))

Assuming decidability of ``S i``, I'd normally then want to use
``inj_pair2_eq_dec`` but that doesn't apply in this case because
``fp_head fp`` and ``fp_head fp'`` aren't syntactically the same. I
also can't rewrite them to be the same because rewriting with
``fp_head fp' = fp_head fp`` would leave the right hand side
ill-typed.

How can I proceed from here? Is there some cleverer version of
``inj_pair2_eq_dec`` that somehow uses the (non-syntactic) base
equality rather than requiring the bases of the sigma types to be
equal?

**Edit:** Thinking about this a little harder, I realise that it
doesn't make sense to ask that the tails are equal (since they are of
different types). But is it possible to prove some form of Leibniz
equality between them based on ``eq_rect``?
|*)

(*|
Answer
******

Issues like these are why many prefer avoiding dependent types in Coq.
I'll answer your question in the case of the Coq sigma type ``{x : T &
S x}``, which can be generalized to other dependent records.

We can express the equality that the dependent component of the pair
should satisfy via a cast function:
|*)

Definition cast {T} (S : T -> Type) {a b : T} (p : a = b) : S a -> S b :=
  match p with eq_refl => fun a => a end.

Definition eq_sig T (S : T -> Type) (a b : T) x y
           (p : existT S a x = existT S b y) :
  {q : a = b & cast S q x = y} :=
  match p in _ = z return {q : a = projT1 z & cast S q x = projT2 z} with
  | eq_refl => existT _ eq_refl eq_refl
  end.

(*|
The ``cast`` function allows us to use an equality ``p : a = b`` to
cast from ``S a`` to ``S b``. The ``eq_sig`` lemma, which I've defined
through a proof term, says that given an equality ``p`` between two
dependent pairs ``existT S a x`` and ``existT S b y``, I can produce
another dependent pair containing:

- An equality ``q : a = b``, and
- a proof that ``x`` and ``y`` are equal *after casting*.

With a similar definition, we can provide a proof principle for
"inducting" on a proof of equality between dependent pairs:
|*)

Definition eq_sig_elim T (S : T -> Type) (a b : T) x y
           (p : existT S a x = existT S b y) :
  forall (R : forall c, S c -> Prop), R a x -> R b y :=
  match p in _ = z
        return forall (R : forall c, S c -> Prop), R a x -> R _ (projT2 z)
  with
  | eq_refl => fun R H => H
  end.

(*|
The shape of the lemma is similar to that of ``eq_sig``, but this time
it says that in the presence of such an equality we can prove an
arbitrary *dependent* predicate ``R b y`` provided a proof of ``R a
x``.

Using such dependent principles can be awkward. The challenge is
finding such an ``R`` that allows you to express your goal: in the
result type above, the type of the second argument of ``R`` is
parametric with respect to the first argument. In many cases of
interest, the first component of the second term, ``y``, is not a
variable, but has a specific shape, which might prevent a direct
generalization.
|*)
