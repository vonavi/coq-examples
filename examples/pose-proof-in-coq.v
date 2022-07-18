(*|
#################
Pose proof in Coq
#################

:Link: https://stackoverflow.com/q/71768615
|*)

(*|
Question
********

I'm trying to prove a theorem in Coq. My current context is:

.. coq:: none
|*)

Variable Entity : Type.
Variables Ps F : Entity -> Entity -> Prop.
Variable C : Entity -> Entity -> Entity -> Prop.

Section Foo.

  Variables s t x : Entity.
  Hypotheses (Pssx : Ps s x) (Fxs : F x s) (IPssx : F x s /\ Ps s x)
             (Ctss : C t s s) (Pstx : Ps t x) (Fxt : F x t).

  Goal C s s s.

(*||*)

    Show. (* .unfold .messages *)
  Abort. (* .none *)

(*|
``F``, ``Ps`` and ``C`` are relations of the theory. I've also Axiom
4:
|*)

  Axiom A4 : forall x s t,
      Ps s x /\ F x s /\ Ps t x /\ F x t -> s = t.

(*|
What I want to do, is to use ``A4`` in the proof, as it will help me
to say that ``s`` and ``t`` are equals. So I've tested: ``pose proof
(A4 x s t).`` A new hypothesis is added: ``H : Ps s x /\ F x s /\ Ps t
x /\ F x t -> s = t``. I know I can destruct the hypothesis ``H``,
prove the premisses and use the conclusion. But I also know that I can
give the premisses directly in the ``pose proof`` command. I want to
do something like ``pose proof (A4 x s t Premisses).`` But I don't
know what to put instead of ``Premisses``.

I tried several solutions:

- composing the hypothesis with ``/\``, such as ``pose proof (A4 x s t
  (Pssx /\ Fxs /\ Pstx /\ Fxt)).`` but I got the error
|*)

  Goal C s s s. (* .none *)
    Fail pose proof (A4 x s t (Pssx /\ Fxs /\ Pstx /\ Fxt)). (* .unfold .messages *)

(*|
- using the ``assert`` command and ``pose proof (A4 x s t H1).``:

  - ``assert (H1 := (Ps s x) /\ (F x s) /\ (Ps t x) /\ (F x t)).`` but
    I got
|*)

    assert (H1 := (Ps s x) /\ (F x s) /\ (Ps t x) /\ (F x t)). (* .none *)
    Fail pose proof (A4 x s t H1). (* .unfold .messages *)
    Undo. (* .none *)

(*|
  - ``assert (H1 := (Pssx) /\ (Fxs) /\ (Pstx) /\ (Fxt)).`` but I got
    \
|*)

    Fail assert (H1 := (Pssx) /\ (Fxs) /\ (Pstx) /\ (Fxt)). (* .unfold .messages *)
  Abort. (* .none *)

(*|
So my question is the following: what should I put instead of
``Premisses`` for my code to work? Is there a command to create new
hypothesis based on other ones? I know how to destruct an hypothesis
into two smaller hypothesis, but I don't know how to compose
hypothesis to create bigger ones.
|*)

(*|
Answer
******

The standard in Coq would be to `curry
<https://en.wikipedia.org/wiki/Currying>`__ your ``A4`` so that
instead of receiving one large conjunction as a premise, it receives
several different premises:
|*)

  Axiom A4' : forall x s t,
      Ps s x -> F x s -> Ps t x -> F x t -> s = t.

(*| Then you can do: |*)

  Goal C s s s. (* .none *)
    pose proof (A4' x s t Pssx Fxs Pstx Fxt).
    Undo. (* .none *)

(*|
If you absolutely need ``A4`` with the conjunctions, you can use
``conj`` (which you can find with ``Print "_ /\ _"``):
|*)

    pose proof (A4 x s t (conj Pssx (conj Fxs (conj Pstx Fxt)))).
