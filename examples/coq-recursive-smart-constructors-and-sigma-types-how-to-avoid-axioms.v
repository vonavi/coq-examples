(*|
######################################################################
Coq: Recursive Smart Constructors and Sigma types, how to avoid axioms
######################################################################

:Link: https://proofassistants.stackexchange.com/q/1048
|*)

(*|
Question
********

I am using a recursive smart constructor to return a sigma type, which
includes the property that the type was constructed in a smart way.
This is very basic compared to the smart constructors and number of
properties I tend to have, but I am already running into problems. I
was wondering if there is a better way to work with smart constructors
and sigma properties. Here is my current example with the problem I
ran into.

We want to represent some nested function calls for a very restricted
language, for example:

::

    and(lt(3, 5), contains("abcd", "bc"))

We represent the parsed ast, like so:
|*)

Inductive Func : Type :=
  mkFunc :
    forall
      (name : nat)
      (params : list Func)
      (hash : nat),
      Func.

(*|
We are still using ``nat`` instead of string to represent the names,
please ignore this, this is just for temporary simplicity. The
``hash`` field is important, because it is used to efficiently compare
functions calls, so that we can reorder and simplify. For example:

- ::

      and(lt(3, 5), contains("abcd", "bc")) => and(contains("abcd",
      "bc"), lt(3, 5))

- ::

      and(lt(3, 5), lt(3, 5)) => lt(3, 5)

- ::

      or(and(lt(3, 5), contains("abcd", "bc")), and(contains("abcd",
      "bc"), lt(3, 5))) => and(contains("abcd", "bc"), lt(3, 5))

For this hash field to mean anything, it needs an associated property
that it was constructed using a smart constructor:
|*)

Require Import List. (* .none *)
Import ListNotations. (* .none *)
Definition get_params (x : Func) : list Func :=
  match x with
  | mkFunc _ params _ => params
  end.

Definition get_hash (x : Func) : nat :=
  match x with
  | mkFunc _ _ hash => hash
  end.

Definition hash_per_elem (state : nat) (x : nat) : nat :=
  31 * state + x.

Fixpoint hash_from_func (f : Func) : nat :=
  match f with
  | mkFunc name params _ =>
      let name_hashed := 31 * 17 * name in
      let param_hashes := map hash_from_func params in
      fold_left hash_per_elem param_hashes name_hashed
  end.

Inductive IsSmart (f : Func) : Prop :=
| isSmart : forall
    (name : nat)
    (params : list Func)
    (hash : nat)
  , f = mkFunc name params hash
    -> hash = hash_from_func f
    -> Forall IsSmart params
    -> IsSmart f.

Ltac destructIsSmart S :=
  let Name := fresh "name" in
  let Params := fresh "params" in
  let Hash := fresh "hash" in
  let Feq := fresh "feq" in
  let Heq := fresh "heq" in
  let HSmarts := fresh "Hsmarts" in
  destruct S as [Name Params Hash Feq Heq HSmarts].

Definition SmartFunc := { func | IsSmart func }.

Ltac destructSmartFunc SF :=
  let F := fresh "f" in
  let S := fresh "s" in
  destruct SF as [F S];
  destructIsSmart S.

Definition get_func (x : SmartFunc) : Func :=
  match x with
  | exist _ f p => f
  end.

Definition get_shash (x : SmartFunc) : nat :=
  match x with
  | exist _ f p => get_hash f
  end.

Definition hash_from_params (hname : nat) (params : list Func): nat :=
  let param_hashes := map hash_from_func params in
  fold_left hash_per_elem param_hashes hname.

Definition hash_from_sparams (hname : nat) (sparams : list SmartFunc): nat :=
  let param_hashes := map get_shash sparams in
  fold_left hash_per_elem param_hashes hname.

Lemma hash_from_params_is_hash_from_sparams:
  forall (hname : nat) (sparams : list SmartFunc),
    hash_from_sparams hname sparams
    =
      hash_from_params hname (map get_func sparams).
Proof.
  (* For the actual proof see https://github.com/katydid/proofs/issues/10 *)
Admitted.

Definition forall_smart_from_sparams (sparams : list SmartFunc) :
  Forall IsSmart (map get_func sparams).
  (* For the actual proof see https://github.com/katydid/proofs/issues/10 *)
Admitted.

Definition smart_from_sparam (s : SmartFunc) : IsSmart (get_func s).
  (* For the actual proof see https://github.com/katydid/proofs/issues/10 *)
Admitted.

Definition mkIsSmart (name : nat) (sparams : list SmartFunc):
  IsSmart
    (mkFunc
       name
       (map get_func sparams)
       (hash_from_sparams (31 * 17 * name) sparams)
    ).
  (* For the actual proof see https://github.com/katydid/proofs/issues/10 *)
Admitted.

Definition mkSmartFunc (name : nat) (sparams : list SmartFunc) : SmartFunc :=
  exist
    _
    (mkFunc
       name
       (map get_func sparams)
       (hash_from_sparams
          (31 * 17 * name)
          sparams
       )
    )
    (mkIsSmart
       name
       sparams
    ).

(*
We can reconstruct our list of SmartFunc again from our list of params
and the Forall property.
*)

Fixpoint get_smart_params'
         (params : list Func)
         (smarts : Forall IsSmart params)
  : list SmartFunc.
  destruct params as [|p ps].
  - exact [].
  - pose proof (Forall_inv smarts) as smart.
    apply Forall_inv_tail in smarts.
    exact (
        (exist _ p smart)
          :: (get_smart_params' ps smarts)
      ).
Defined.

(* But when we try to retreive our forall property about params from
our SmartFunc then we get the error. *)

Theorem get_smart_params (s : SmartFunc) : { params | Forall IsSmart params }.
  destruct s as [f is].
  Fail destruct is. (* .fails .unfold .in .messages *)

(*|
I have seen that it is possible to use
``constructive_indefinite_description``, but this uses an axiom. I was
wondering if there was a way to better work with recursive smart
constructors and sigma types to avoid needing axioms?

Note in `this GitHub issue
<https://github.com/katydid/proofs/issues/10>`__ you will find copy
and paste-able code, that you can play around with, if that helps.
|*)

(*|
Answer (Li-yao Xia)
*******************

You can first instantiate the proof-relevant part of the goal using
``exists``, leaving you with a goal in ``Prop`` so you can then
destruct hypotheses in ``Prop``.
|*)

  exists (get_params f). (* or: apply (exist _ (get_params f)). *)
  destruct is.
Abort. (* .none *)

(*|
Answer
******

Some simpler examples to show when we can and cannot destruct a ``Prop``.
=========================================================================

We can't destruct a ``Prop``, when our goal contains something in ``Set``:
--------------------------------------------------------------------------
|*)

Theorem case_and_point_1 : forall (m : nat), m > 0 -> { n | n > 0 }.
Proof.
  intros m H.
  Fail induction H.
  (*
    We can't destruct a Prop, when our goal contains something in Set.
   *)
  exists 1.
  (*
    Now we only need to return a Prop (1 > 0), which means we can
    destruct a Prop.
   *)
  induction H.
Abort.

(*|
We can't destruct a ``Prop``, when our goal is in ``Set``:
----------------------------------------------------------
|*)

Theorem case_and_point_2 : 3 > 2 -> nat.
Proof.
  intros H.
  Fail induction H.
  (*
    We can't destruct a Prop, when our goal is in Set.
   *)
  exact 1.
Qed.

(*|
We can destruct a ``Prop``, when our goal does not contain something in ``Set``, even if it is in ``Type``:
-----------------------------------------------------------------------------------------------------------
|*)

Inductive myType : Type :=
  mkMyType: myType.

Inductive myPropOnType (t : myType) : Prop :=
  isMyPropOnType: myPropOnType t.

Theorem case_and_point_3:
  3 > 2 -> { t | myPropOnType t }.
Proof.
  intros H.
  (*
    We can destruct a Prop, when our goal does not contain something
    in Set, even if it is in Type.
   *)
  induction H.
Abort.

(*|
We can't destruct a ``Prop``, when our goal contains something in ``Set``:
--------------------------------------------------------------------------
|*)

Inductive mySet : Set :=
  mkMySet : mySet.

Inductive myPropOnSet (s : mySet) : Prop :=
  isMyPropOnSet: myPropOnSet s.

Theorem case_and_point_4 : 3 > 2 -> { s | myPropOnSet s }.
Proof.
  intros H.
  (*
    We can't destruct a Prop, when our goal contains something in Set:
   *)
  Fail induction H.
Abort.

(*|
We can destruct a ``Prop``, if it is guaranteed to only return a ``Prop``.
--------------------------------------------------------------------------
|*)

Theorem case_and_point_6 : 3 > 2 /\ 1 > 0 -> nat.
Proof.
  intros H.
  (*
    We can destruct a Prop, if it is guaranteed to only return a Prop.
    This works for conjunction, which is made up of two props, but
    will fail for Forall, which can possibly destruct to the empty
    list, which is in Set.
   *)
  destruct H as [H0 H1].
  Fail destruct H0.
  exact 1.
Qed.

(*|
We can use theorems to destruct a ``Prop`` other ``Prop``\ s.
-------------------------------------------------------------
|*)

Lemma seven : 3 > 2 /\ 1 > 0 -> 7 = 7.
Admitted.

Theorem case_and_point_7 : 3 > 2 /\ 1 > 0 -> nat.
Proof.
  intros H.
  (*
    We can use theorems to destruct a Prop other Props.
   *)
  apply seven in H.
Abort.
