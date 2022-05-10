(*|
####################################################
Problems with dependent types in Coq proof assistant
####################################################

:Link: https://stackoverflow.com/q/43453365
|*)

(*|
Question
********

Consider the following simple expression language:
|*)

Require Import Arith_base List. (* .none *)
Inductive Exp : Set :=
| EConst : nat -> Exp
| EVar   : nat -> Exp
| EFun   : nat -> list Exp -> Exp.

(*| and its wellformedness predicate: |*)

Definition Env := list nat.

Inductive WF (env : Env) : Exp -> Prop :=
| WFConst : forall n, WF env (EConst n)
| WFVar   : forall n, In n env -> WF env (EVar n)
| WFFun   : forall n es, In n env ->
                         Forall (WF env) es ->
                         WF env (EFun n es).

(*|
which basically states that every variable and function symbols must
be defined in the environment. Now, I want to define a function that
states the decidability of ``WF`` predicate:
|*)

Definition WFDec (env : Env) : forall e, {WF env e} + {~ WF env e}.
  refine (fix wfdec e : {WF env e} + {~ WF env e} :=
            match e as e' return e = e' -> {WF env e'} + {~ WF env e'} with
            | EConst n => fun _ => left _ _
            | EVar n => fun _ =>
                          match in_dec eq_nat_dec n env with
                          | left _ _ => left _ _
                          | right _ _ => right _ _
                          end
            | EFun n es => fun _ =>
                             match in_dec eq_nat_dec n env with
                             | left _ _ => _
                             | right _ _ => right _ _
                             end
            end (eq_refl e)); clear wfdec; subst; eauto.
Abort. (* .none *)

(*|
The trouble is how to state that ``WF`` predicate holds or not for a
list of expressions in the ``EFun`` case. My obvious guess was:

.. code-block:: coq

    ...
    match Forall_dec (WF env) wfdec es with
    ...

But Coq refuses it, arguing that the recursive call ``wfdec`` is
ill-formed. My question is: Is it possible to define decidability of
such wellformedness predicate without changing the expression
representation?

The complete working code is at the following `gist
<https://gist.github.com/rodrigogribeiro/132e4feca910f40198242d3da3eca040>`__.
|*)

(*|
Answer (ejgallego)
******************

As a temporal workaround you can define ``wf`` as:
|*)
From mathcomp Require Import all_ssreflect. (* .none *)
Definition wf (env : Env) := fix wf (e : Exp) : bool :=
    match e with
    | EConst _ => true
    | EVar v   => v \in env
    | EFun v l => [&& v \in env & all wf l]
    end.

(*|
which is usually way more convenient to use. However, this definition
will be pretty useless due to Coq generating the wrong induction
principle for ``exp``, as it doesn't detect the list. What I usually
do is to fix the induction principle manually, but this is costly.
Example:
|*)

Reset Initial. (* .none *)
From Coq Require Import List.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Import Prenex Implicits.

Section ReflectMorph.

  Lemma and_MR P Q b c : reflect P b -> reflect Q c -> reflect (P /\ Q) (b && c).
  Proof. by move=> h1 h2; apply: (iffP andP) => -[/h1 ? /h2 ?]. Qed.

  Lemma or_MR P Q b c : reflect P b -> reflect Q c -> reflect (P \/ Q) (b || c).
  Proof. by move=> h1 h2; apply: (iffP orP) => -[/h1 | /h2]; auto. Qed.

End ReflectMorph.

Section IN.
  Variables (X : eqType).

  Lemma InP (x : X) l : reflect (In x l) (x \in l).
  Proof.
    elim: l => [|y l ihl]; first by constructor 2.
    by apply: or_MR; rewrite // eq_sym; exact: eqP.
  Qed.

End IN.

Section FORALL.

  Variables (X : Type) (P : X -> Prop).
  Variables (p : X -> bool).

  Lemma Forall_inv x l : Forall P (x :: l) -> P x /\ Forall P l.
  Proof. by move=> U; inversion U. Qed.

  Lemma ForallP l : (forall x, In x l -> reflect (P x) (p x)) ->
                    reflect (Forall P l) (all p l).
  Proof.
    elim: l => [|x l hp ihl /=]; first by constructor.
    have/hp {hp}hp : forall x : X, In x l -> reflect (P x) (p x).
    by move=> y y_in; apply: ihl; right.
    have {ihl} ihl := ihl _ (or_introl erefl).
    by apply: (iffP andP) => [|/Forall_inv] [] /ihl hx /hp hall; constructor.
  Qed.

End FORALL.

Inductive Exp : Type :=
| EConst : nat -> Exp
| EVar   : nat -> Exp
| EFun   : nat -> list Exp -> Exp.

Lemma Exp_rect_list (P : Exp -> Type) :
  (forall n : nat, P (EConst n)) ->
  (forall n : nat, P (EVar n)) ->
  (forall (n : nat) (l : seq Exp),
      (forall x, In x l -> P x) -> P (EFun n l)) -> forall e : Exp, P e.
Admitted.

Definition Env := list nat.

Definition wf (env : Env) := fix wf (e : Exp) : bool :=
    match e with
    | EConst _ => true
    | EVar v   => v \in env
    | EFun v l => [&& v \in env & all wf l]
    end.

Inductive WF (env : Env) : Exp -> Prop :=
| WFConst : forall n, WF env (EConst n)
| WFVar   : forall n, In n env -> WF env (EVar n)
| WFFun   : forall n es, In n env ->
                         Forall (WF env) es ->
                         WF env (EFun n es).

Lemma WF_inv env e (wf : WF env e) :
  match e with
  | EConst n  => True
  | EVar n    => In n env
  | EFun n es => In n env /\ Forall (WF env) es
  end.
Proof. by case: e wf => // [n | n l] H; inversion H. Qed.

Lemma wfP env e : reflect (WF env e) (wf env e).
Proof.
  elim/Exp_rect_list: e => [n | n | n l ihe] /=; try repeat constructor.
  by apply: (iffP idP) => [/InP | /WF_inv/InP //]; constructor.
  apply: (iffP andP) => [[/InP ? /ForallP H] | /WF_inv[/InP ? /ForallP]].
  by constructor => //; exact: H.
  by auto.
Qed.

(*|
Answer (Arthur Azevedo De Amorim)
*********************************

The problem is that ``Forall_dec`` is defined as opaque in the
standard library (that is, with ``Qed`` instead of ``Defined``).
Because of that, Coq does not know that the use of ``wfdec`` is valid.

The immediate solution to your problem is to redefine ``Forall_dec``
so that it is transparent. You can do this by printing the proof term
that Coq generates and pasting it in your source file. I've added a
`gist
<https://gist.github.com/anonymous/5b3fdc11871e42b3e9cfe006f6d8cc76>`__
here with a complete solution.

Needless to say, this approach lends itself to bloated, hard to read,
and hard to maintain code. As ejgallego was pointing out in his
answer, your best bet in this case is probably to define a Boolean
function that decides ``WF``, and use that instead of ``WFDec``. The
only problem with his approach, as he said, is that you will need to
write your own induction principle to ``Exp`` in order to prove that
the Boolean version indeed decides the inductive definition. Adam
Chlipala's CPDT has a `chapter
<http://adam.chlipala.net/cpdt/html/InductiveTypes.html>`__ on
inductive types that gives an example of such an induction principle;
just look for "nested inductive types".
|*)
