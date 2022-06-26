(*|
############################################################
Existential quantifier in Coq impredicative logic (System F)
############################################################

:Link: https://stackoverflow.com/q/19083196
|*)

(*|
Question
********

I was trying to code into Coq logical connectives encoded in lambda
calculus with type à la System F. Here is the bunch of code I wrote
(standard things, I think)
|*)

Definition True := forall X : Prop, X -> X.

Lemma I : True.
Proof.
  unfold True. intros. apply H.
Qed.

Section s.
  Variables A B : Prop.

  (* conjunction *)

  Definition and := forall X : Prop, (A -> B -> X) -> X.
  Infix "/\" := and.

  Lemma and_intro : A -> B -> A /\ B.
  Proof using A B.
    intros HA HB. split.
    - apply HA.
    - apply HB.
  Qed.

  Lemma and_elim_l : A /\ B -> A.
  Proof using A B.
    intros H. destruct H as [HA HB]. apply HA.
  Qed.

  Lemma and_elim_r : A /\ B -> B.
  Proof using A B.
    intros H. destruct H as [HA HB]. apply HB.
  Qed.

  (* disjunction *)

  Definition or := forall X : Prop, (A -> X) -> (B -> X) -> X.
  Infix "\/" := or.

  Lemma or_intro_l : A -> A \/ B.
  Proof using A B.
    intros HA. left. apply HA.
  Qed.

  Lemma or_elim : forall C : Prop, A \/ B -> (A -> C) -> (B -> C) -> C.
  Proof using A B.
    intros C HOR HAC HBC. destruct HOR.
    apply (HAC H).
    apply (HBC H).
  Qed.

  (* falsity *)

  Definition False := forall Y : Prop, Y.

  Lemma false_elim : False -> A.
  Proof using A.
    unfold False. intros. apply (H A).
  Qed.

End s.

(*|
Basically, I wrote down the elimination and introduction laws for
conjunction, disjunction, true and false. I am not sure of having done
thing correctly, but I think that things should work that way. Now I
would like to define the existential quantification, but I have no
idea of how to proceed. Does anyone have a suggestion?
|*)

(*|
Answer
******

Existential quantification is just a generalization of conjunction,
where the type of the second component of the pair depends on the
value of the first component. When there's no dependency they're
equivalent:
|*)

Goal forall P1 P2 : Prop, (exists _ : P1, P2) <-> P1 /\ P2.
Proof. split; intros [H1 H2]; eauto. Qed.

(*|
`Coq'Art <http://www.labri.fr/perso/casteran/CoqArt/index.html>`__ has
a section on impredicativity starting at page 130.
|*)

Print ex. (* .unfold .messages *)

Locate "exists". (* .unfold .messages *)

(*|
The problem with impredicative definitions (unless I'm mistaken) is
that there's no dependent elimination. It's possible prove
|*)

Goal forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x : A, P x -> Q) -> (exists x, P x) -> Q.
Admitted. (* .none *)

(*| but not |*)

Goal forall (A : Type) (P : A -> Prop) (Q : (exists x, P x) -> Prop),
    (forall (x : A) (H : P x), Q (ex_intro P x H)) ->
    forall H : exists x, P x, Q H.
Abort. (* .none *)
