(*|
How to enumerate set in Coq Ensemble
====================================

https://stackoverflow.com/questions/68789154/how-to-enumerate-set-in-coq-ensemble
|*)

(*|
Question
--------

How do you prove `enumerateSingletonPowerset`?
|*)

Require Import Coq.Sets.Ensembles.

Definition emptyOnly A := Singleton _ (Empty_set A).

Theorem enumerateSingletonPowerset A s (inc : Included _ s (emptyOnly A)):
  Same_set _ s (Empty_set _) \/ Same_set _ s (emptyOnly A).
Abort. (* .none *)

(*|
I'm using `Same_set` to avoid extensionality. (Either way is fine.)

Conceptually, it seems simple to just say I have `{{}}` so the
powerset is `{{}, {{}}}` and that's it. But, it's not clear how to say
anything like that with these primitives on their own.

I'd be tempted to try destructing on if empty set was in the set s.
But, since Emsemble is propositional, checking set membership is not
generally decidable. A first thought is
|*)

Axiom In_dec : forall A a e, In A e a \/ ~In A e a.

Theorem ExcludedMiddle P : P \/ ~P.
  apply (In_dec _ tt (fun _ => P)).
Qed.

(*|
But, that is too powerful and immediately puts me into classical
logic. The finite case is easy, but I plan on dealing with larger sets
(e.g. Reals), so In and Included would not generally be computable.
Are there axioms I could add that could allow In and Included to
pretend to be decidable without making everything else decidable too?

Edit: Changed from pair to singleton since quantity isn't important.
|*)

(*|
Answer
------

I found a way to get it to work without any additional axioms using
the "not not" technique from "Classical Mathematics for a Constructive
World" https://arxiv.org/pdf/1008.1213.pdf

(I haven't tried to clean up the proofs at all, just to get it to type
check. Sorry for weird phrasing in proofs.)
|*)

Reset emptyOnly. (* .none *)
Require Import Coq.Sets.Ensembles.

(* Classical reasoning without extra axioms. *)
Definition stable P := ~~P -> P.

Theorem stable_False : stable False.
  unfold stable; intros nnF.
  apply nnF; intros f.
  apply f.
Qed.

Definition orW P Q := ~(~P /\ ~Q).

Definition exW {A} (P : A -> Prop) := ~(forall a, ~P a).

Theorem exW_strengthen {A} P Q (stQ : stable Q) (exQ : (exists a, P a) -> Q)
        (exWP : exW (fun (a : A) => P a)) : Q.
  apply stQ; hnf; intros.
  apply exWP; intros; hnf; intros.
  apply H; apply exQ; apply (ex_intro _ _ H0).
Qed.

(* Ensembles *)
Definition emptyOnly A := Singleton _ (Empty_set A).

Theorem notEmpty_In A (s : Ensemble A) (ne : ~ Same_set _ s (Empty_set _)) :
  exW (fun a => In _ s a).
  hnf; intros; apply ne; clear ne.
  apply conj; hnf; intros; [ | destruct H0 ].
  apply (False_ind _ (H _ H0)).
Qed.

Theorem enumerateSingletonPowerset A s (inc : Included _ s (emptyOnly A)):
  orW (Same_set _ s (Empty_set _)) (Same_set _ s (emptyOnly A)).
  hnf; intros; destruct H.
  apply notEmpty_In in H.
  revert H; apply exW_strengthen; intros; [ apply stable_False | ]; destruct H.
  apply H0; clear H0; apply conj; hnf; intros; [ apply (inc _ H0) | ].
  destruct H0.
  destruct (inc _ H).
  apply H.
Qed.

(*|
So, by rephrasing the theorem to use weak or, it is now possible to
prove it directly, and without appealing to the structure of A, that
membership is decidable, or classical logic.
|*)
