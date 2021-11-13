(*|
How can I construct terms in first-order logic using Coq?
=========================================================

https://stackoverflow.com/questions/64841759/how-can-i-construct-terms-in-first-order-logic-using-coq
|*)

(*|
Question
--------

I'm trying to define first-order logic in Coq and beginning at terms.
Supposing that `c1` and `c2` are two constant symbols, variables are
`nat` and `f1` and `f2` are two function symbols whose arities are 1
and 2 respectively, I wrote the following code.
|*)

Definition var := nat.

Inductive const : Type :=
| c1
| c2.

Inductive term : Type :=
| Con : const -> term
| Var : var -> term
| F1 : term -> term
| F2 : term -> term -> term.

(*| Then, I got a desired induction. |*)

Check term_ind. (* .unfold *)

(*|
Then I wanted to separate functions from the definition of `term`, so
I rewrote the above.
|*)

Reset term. (* .none *)
(*Idea A*)
Inductive funct {X : Type} : Type :=
| f1 : X -> funct
| f2 : X -> X -> funct.

Inductive term : Type :=
| Con : const -> term
| Var : var -> term
| Fun : @funct term -> term.

Check term_ind. (* .unfold *)
Check funct_ind term. (* .unfold *)

Reset term. (* .none *) Reset funct. (* .none *)
(*Idea B*)
Inductive term : Type :=
| Con : const -> term
| Var : var -> term
| Fun : funct -> term
with funct : Type :=
| f1 : term -> funct
| f2 : term -> term -> funct.

Check term_ind. (* .unfold *)
Check funct_ind. (* .unfold *)

(*|
However, both ways seem not to generate the desired induction because
they don't have induction hypotheses.

How can I construct `term` with functions separated from the
definition of `term` without loss of proper induction?

Thanks.
|*)

(*|
Answer
------

This is a common issue with Coq: the induction principles generated
for mutually inductive types and for types with complex recursive
occurrences are too weak. Fortunately, this can be fixed by defining
the induction principles by hand. In your case, the simplest approach
is to use the mutually inductive definition, since Coq can lend us a
hand for proving the principle.

First, let ask Coq not to generate its weak default induction
principle:
|*)

Reset term. (* .none *) Reset funct. (* .none *)
Unset Elimination Schemes.
Inductive term : Type :=
| Con : const -> term
| Var : var -> term
| Fun : funct -> term
with funct : Type :=
| f1 : term -> funct
| f2 : term -> term -> funct.
Set Elimination Schemes.

(*|
(This is not strictly necessary, but it helps keeping the global
namespace clean.)

Now, let us use the `Scheme` command to generate a mutual induction
principle for these types:
|*)

Scheme term_ind' := Induction for term Sort Prop
  with funct_ind' := Induction for funct Sort Prop. (* .unfold *)

(*|
This principle is already powerful enough for us to prove properties
of `term`, but it is a bit awkward to use, since it requires us to
specify a property that we want to prove about the `funct` type as
well (the `P0` predicate). We can simplify it a bit to avoid
mentioning this auxiliary predicate: all we need to know is that the
terms inside the function calls satisfy the predicate that we want to
prove.
|*)

Definition lift_pred (P : term -> Prop) (f : funct) : Prop :=
  match f with
  | f1 t => P t
  | f2 t1 t2 => P t1 /\ P t2
  end.

Lemma term_ind (P : term -> Prop) :
  (forall c, P (Con c)) ->
  (forall v, P (Var v)) ->
  (forall f, lift_pred P f -> P (Fun f)) ->
  forall t, P t.
Proof.
  intros HCon HVar HFun.
  apply (term_ind' P (lift_pred P)); trivial.
  now intros t1 IH1 t2 IH2; split.
Qed.

(*|
If you prefer, you can also rewrite this to look more like the
original induction principle:
|*)

Reset term_ind.
Lemma term_ind (P : term -> Prop) :
  (forall c, P (Con c)) ->
  (forall v, P (Var v)) ->
  (forall t, P t -> P (Fun (f1 t))) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (Fun (f2 t1 t2))) ->
  forall t, P t.
Proof.
  intros HCon HVar HFun_f1 HFun_f2.
  apply (term_ind' P (lift_pred P)); trivial.
  - now intros [t | t1 t2]; simpl; intuition.
  - now simpl; intuition.
Qed.

(*|
**Edit**

To get an induction principle for your other approach, you have to
write a proof term by hand:
|*)

Reset var. (* .none *)
Definition var := nat.

Inductive const : Type :=
| c1
| c2.

Inductive funct (X : Type) : Type :=
| f1 : X -> funct X
| f2 : X -> X -> funct X.
Arguments f1 {X} _.
Arguments f2 {X} _ _.

Unset Elimination Schemes.
Inductive term : Type :=
| Con : const -> term
| Var : var -> term
| Fun : funct term -> term.
Set Elimination Schemes.

Definition term_ind (P : term -> Type)
           (HCon : forall c, P (Con c))
           (HVar : forall v, P (Var v))
           (HF1  : forall t, P t -> P (Fun (f1 t)))
           (HF2  : forall t1, P t1 -> forall t2, P t2 -> P (Fun (f2 t1 t2))) :
  forall t, P t :=
  fix loop (t : term) : P t :=
    match t with
    | Con c => HCon c
    | Var v => HVar v
    | Fun (f1 t) => HF1 t (loop t)
    | Fun (f2 t1 t2) => HF2 t1 (loop t1) t2 (loop t2)
    end.
