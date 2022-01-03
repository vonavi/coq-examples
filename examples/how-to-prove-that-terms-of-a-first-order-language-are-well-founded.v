(*|
###################################################################
How to prove that terms of a first-order language are well-founded?
###################################################################

:Link: https://stackoverflow.com/q/52087304
|*)

(*|
Question
********

Currently, I've started working on proving theorems about first-order
logic in Coq (`VerifiedMathFoundations
<https://github.com/georgydunaev/VerifiedMathFoundations>`__). I've
proved deduction theorem, but then I got stuck with lemma 1 for
theorem of correctness. So I've formulated one elegant piece of the
lemma compactly and I invite the community to look at it. That is an
incomplete the proof of well-foundness of the terms. How to get rid of
the pair of ``admit``\ s properly?
|*)

(* PUBLIC DOMAIN *)
Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.

Definition SetVars  := nat.
Definition FuncSymb := nat.
Definition PredSymb := nat.
Record FSV :=
  {
  fs : FuncSymb;
  fsv : nat;
  }.
Record PSV :=
  MPSV {
      ps : PredSymb;
      psv : nat;
    }.
Inductive Terms : Type :=
| FVC :> SetVars -> Terms
| FSC (f : FSV) : Vector.t Terms (fsv f) -> Terms.

Definition rela : forall (x y : Terms), Prop.
Proof.
  fix rela 2. intros x y. destruct y as [s|f t].
  - exact False.
  - refine (or _ _).
    exact (Vector.In x t).
    simple refine (@Vector.fold_left Terms Prop _ False (fsv f) t).
    intros Q e.
    exact (or Q (rela x e)).
Defined.

Definition snglV {A} (a : A) := Vector.cons A a 0 (Vector.nil A).

Definition wfr : @well_founded Terms rela.
Proof.
  clear. unfold well_founded.
  assert (H : forall (n:Terms) (a:Terms), (rela a n) -> Acc rela a).
  { fix iHn 1. destruct n.
    - simpl. intros a b. destruct b.
    - simpl. intros a Q. destruct Q as [L|R].
      + admit.
        (* smth like apply Acc_intro. intros m Hm. apply (iHn a). exact Hm. *)
      + admit.
        (* like in /Arith/Wf_nat.v *)
  }
  intros a. simple refine (H _ _ _).
  exact (FSC (Build_FSV 0 1) (snglV a)).
  simpl. apply or_introl. constructor.
Fail Defined. (* .fails *)
Admitted. (* .none *)

(*|
It is also available here: `pastebin
<https://pastebin.com/UqpxM5Xb>`__.

*Update:* At least transitivity is needed for well-foundness. I also
started a proof, but didn't finished.
|*)

Fixpoint Tra (a b c : Terms) (Hc : rela c b) (Hb : rela b a) {struct a} :
  rela c a.
Proof.
  destruct a.
  - simpl in * |- *. exact Hb.
  - simpl in * |- *. destruct Hb.
    + apply or_intror. revert f t H . fix RECU 1. intros f t H.
    (* ... *)
Admitted.

(*|
Answer
******

You can do it by defining a height function on ``Terms``, and showing
that decreasing ``rela`` implies decreasing heights:
|*)

Reset SetVars. (* .none *)
Require Export Coq.Vectors.Vector.
Require Export Coq.Lists.List.
Require Import Bool.Bool.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.

Definition SetVars  := nat.
Definition FuncSymb := nat.
Definition PredSymb := nat.
Record FSV :=
  {
  fs : FuncSymb;
  fsv : nat;
  }.
Record PSV :=
  MPSV {
      ps : PredSymb;
      psv : nat;
    }.

Unset Elimination Schemes.
Inductive Terms : Type :=
| FVC :> SetVars -> Terms
| FSC (f : FSV) : Vector.t Terms (fsv f) -> Terms.
Set Elimination Schemes.

Definition Terms_rect (T : Terms -> Type)
           (H_FVC : forall sv, T (FVC sv))
           (H_FSC : forall f v,
               (forall n, T (Vector.nth v n)) -> T (FSC f v)) :=
  fix loopt (t : Terms) : T t :=
    match t with
    | FVC sv  => H_FVC sv
    | FSC f v =>
      let fix loopv s (v : Vector.t Terms s) : forall n, T (Vector.nth v n) :=
          match v with
          | @Vector.nil _ => Fin.case0 _
          | @Vector.cons _ t _ v =>
            fun n =>
              Fin.caseS' n (fun n => T (Vector.nth (Vector.cons _ t _ v) n))
                         (loopt t)
                         (loopv _ v)
          end in
      H_FSC f v (loopv _ v)
    end.

Definition Terms_ind := Terms_rect.

Fixpoint height (t : Terms) : nat :=
  match t with
  | FVC _ => 0
  | FSC f v => S (Vector.fold_right (fun t acc => Nat.max acc (height t)) v 0)
  end.

Definition rela : forall (x y : Terms), Prop.
Proof.
  fix rela 2. intros x y. destruct y as [s|f t].
  - exact False.
  - refine (or _ _). exact (Vector.In x t).
    simple refine (@Vector.fold_left Terms Prop _ False (fsv f) t).
    intros Q e. exact (or Q (rela x e)).
Defined.

Require Import Lia.

Definition wfr : @well_founded Terms rela.
Proof.
  apply (Wf_nat.well_founded_lt_compat _ height).
  intros t1 t2. induction t2 as [sv2|f2 v2 IH]; simpl; try easy.
  intros [t_v|t_sub]; apply Lt.le_lt_n_Sm.
  { clear IH. induction t_v; simpl; lia. }
  revert v2 IH t_sub. generalize (fsv f2). clear f2.
  intros k v2 IH t_sub.
  enough (H : exists n, rela t1 (Vector.nth v2 n)).
  { destruct H as [n H]. apply IH in H. clear IH t_sub.
    transitivity (height (Vector.nth v2 n)); try lia; clear H.
    induction v2 as [|t2 m v2 IHv2].
    - inversion n.
    - apply (Fin.caseS' n); clear n; simpl; try lia.
      intros n. specialize (IHv2 n). lia. }
  clear IH.
  assert (H : Vector.fold_right (fun t Q => Q \/ rela t1 t) v2 False).
  { revert t_sub. generalize False.
    induction v2 as [|t2 n v2]; simpl in *; trivial.
    intros P H. specialize (IHv2 _ H). clear H.
    induction v2 as [|t2' n v2 IHv2']; simpl in *; tauto. }
  clear t_sub.
  induction v2 as [|t2 k v2 IH]; simpl in *; try easy.
  destruct H as [H|H].
  - apply IH in H. destruct H as [n Hn]. now (exists (Fin.FS n)).
  - now exists Fin.F1.
Qed.

(*|
(Note the use of the custom induction principle, which is needed
because of the nested inductives.)

This style of development, however, is too complicated. Avoiding
certain pitfalls would greatly simplify it:

1. The Coq standard vector library is too hard to use. The issue here
   is exacerbated because of the nested inductives. It would probably
   be better to use plain lists and have a separate well-formedness
   predicate on terms.

2. Defining a relation such as ``rela`` in proof mode makes it harder
   to read. Consider, for instance, the following simpler alternative:
|*)

Reset rela. (* .none *)
Fixpoint rela x y :=
  match y with
  | FVC _ => False
  | FSC f v =>
    Vector.In x v \/
    Vector.fold_right (fun z P => rela x z \/ P) v False
  end.

(*|
3. Folding left has a poor reduction behavior, because it forces us to
   generalize over the accumulator argument to get the induction to go
   through. This is why in my proof I had to switch to a
   ``fold_right``.
|*)
