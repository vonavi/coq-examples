(*|
################
Subtyping in Coq
################

:Link: https://stackoverflow.com/q/41306638
|*)

(*|
Question
********

I defined Subtype as follows
|*)

Record Subtype {T : Type} (P : T -> Prop) := {
    subtype       :> Type;
    subtype_inj   :> subtype -> T;
    subtype_isinj : forall s t : subtype,
      (subtype_inj s = subtype_inj t) -> s = t;
    subtype_h     : forall x : T, P x -> (exists s : subtype,x = subtype_inj s);
    subtype_h0    : forall s : subtype, P (subtype_inj s)
  }.

(*| Can the following theorem be proven? |*)

Theorem Subtypes_Exist : forall {T} (P : T -> Prop), Subtype P.
Abort. (* .none *)

(*|
If not, is it provable from any well-known compatible axiom? Or Can I
add this as an axiom? Would it conflict with any usual axiom? (like
extensionality, functional choice, etc.)
|*)

(*|
Answer
******

Your definition is practically identical to the one of MathComp;
indeed, what you are missing mainly is injectivity due to proof
relevance.

For that, I am afraid you will need to assume propositional
irrelevance:
|*)

Require Import ProofIrrelevance.

Theorem Subtypes_Exist : forall {T} (P : T -> Prop), Subtype P.
Proof.
  intros T P; set (subtype_inj := @proj1_sig T P).
  apply (@Build_Subtype _ _ { x | P x} subtype_inj).
  + intros [s Ps] [t Pt]; simpl; intros ->.
    now rewrite (proof_irrelevance _ Ps Pt).
  + now intros x Px; exists (exist _ x Px).
  + now intro H; destruct H.
Qed.

(*|
You can always restrict you predicate ``P`` to a type which is
effectively proof-irrelevant, of course.
|*)
