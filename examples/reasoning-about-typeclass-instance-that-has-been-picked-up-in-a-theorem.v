(*|
########################################################################
reasoning about typeclass instance that has been picked up in a theorem?
########################################################################

:Link: https://stackoverflow.com/q/50889650
|*)

(*|
Question
********
|*)

Class Action (Actor: Type) (Acted: Type) :=
  {
  act : Actor -> Acted -> Acted;
  someProof: forall (a: Actor), a = a;
  }.

#[refine] Instance natListAction: Action nat (list nat) :=
  {
  act (n: nat) (l: list nat) := cons n l;
  }.
Proof.
    auto.
Qed.

Lemma natListAction_is_cons: forall (n: nat) (l: list nat),
    act n l = cons n l.
Proof.
  intros. unfold act.
  (** I cannot unfold it, since I have someProof.
      If I remove this, this unfold works **)
  Fail unfold natListAction. (* .fails *)
Abort.

(*|
What I actually want is this: because I know that ``act`` resolves to
``natListAction``, I know that ``act = cons``. Hence, the lemma should
go through.

If I do not have the ``someProof`` in my ``Action`` class, then I can
``unfold natListAction`` and stuff works. But now, I am unable to do
so.

However, how do I convince coq that ``act = cons`` in this case?
|*)

(*|
Answer
******

I found the answer on another SO thread: `Coq: unfolding typeclass
instances
<https://stackoverflow.com/questions/24111816/coq-unfolding-class-instances>`__.

Ending the ``Proof`` section with a ``Qed`` makes it opaque. Instead,
end the proof with a ``Defined`` and it will go through.

For the sake of completeness, here is the final proof:
|*)

Reset Initial. (* .none *)
Class Action (Actor: Type) (Acted: Type) :=
  {
  act : Actor -> Acted -> Acted;
  someProof: forall (a: Actor), a = a;
  }.

#[refine] Instance natListAction: Action nat (list nat) :=
  {
  act (n: nat) (l: list nat) := cons n l;
  }.
Proof.
  auto.
  (** vvv Notice the change! this is now "Defined" vvv **)
Defined.

Lemma natListAction_is_cons: forall (n: nat) (l: list nat),
    act n l = cons n l.
Proof.
  intros. unfold act. unfold natListAction. reflexivity.
Qed.

(*|
----

**A:** Observe that ``reflexivity`` alone is enough to do the proof.

**Q:** ah, nice. Because ``reflexivity`` simplifies things?

**A:** Correct. ``reflexivity`` is a pretty complex tactic with `lots
of fallbacks <https://stackoverflow.com/q/46227271/2747511>`__. So it
can do ``intros`` and the rest of it follows by computation, which
includes unfoldings a.k.a. ``delta`` reduction.

**A:** Technically, the reason ``reflexivity`` can solve this is
because (a) ``reflexivity`` does ``intros``, and (b), the term ``fun n
l => eq_refl`` typechecks as a proof of your theorem. It is not that
``reflexivity`` is doing ``delta`` reduction here, but that judgmental
equality is modulo delta.
|*)
