(*|
###################################################################
Stuck on the proof of a simple Lemma: which induction should I use?
###################################################################

:Link: https://stackoverflow.com/q/73018759
|*)

(*|
Question
********

I have the following structures:
|*)

Require Import List Arith. (* .none *)
Inductive instr : Set :=
| Select    : nat -> instr
| Backspace : instr.

Definition prog := list instr.

(*| and the following function: |*)

Fixpoint Forward (input output : list nat) : option prog :=
  match input with
  | nil => match output with
           | nil => Some nil
           | y :: r => None
           end
  | x :: rest =>
      match output with
      | nil => match rest with
               | nil => None
               | xx :: rrest => match Forward rrest nil with
                                | Some pp => Some (Select x :: Backspace :: pp)
                                | None => None
                                end
               end
      | y :: r => if beq_nat x y then
                    match Forward rest r with
                    | Some pp => Some (Select x :: pp)
                    | None => None
                    end
                  else
                    match rest with
                    | nil => None
                    | xx :: rrest =>
                        match Forward rrest output with
                        | Some pp => Some (Select x :: Backspace :: pp)
                        | None => None
                        end
                    end
      end
  end.

(*| Now I'd like to prove this simple Lemma: |*)

Lemma app_forward :
  forall (p p' : prog) (input1 input2 output : list nat),
    Forward input1 output = Some p ->
    Forward input2 nil = Some p' ->
    Forward (input1 ++ input2) output = Some (p ++ p').
Abort. (* .none *)

(*|
Note: As mentioned in the answer bellow, the more general form of the
lemma is false:
|*)

Lemma not_app_forward :
  forall (p p' : prog) (input1 input2 output1 output2 : list nat),
    Forward input1 output1 = Some p ->
    Forward input2 output2 = Some p' ->
    Forward (input1 ++ input2) (output1 ++ output2) = Some (p ++ p').
Abort. (* .none *)

(*|
Whatever induction principle I use, I'm stuck.

For example, I've tried this induction pattern:
|*)

Definition list_pair_induction {A : Type} :
  forall (P : list A -> Prop),
    P nil ->
    (forall a, P (a :: nil)) ->
    (forall a b tl, P tl -> P (a :: b :: tl)) ->
    forall l, P l.
Proof.
  intros P Pn P1 Prec. fix tsli 1. intros [| x l].
  - exact Pn.
  - generalize (tsli l).
    destruct l as [| y tl]; intros Pl.
    + exact (P1 x).
    + apply Prec. exact (tsli tl).
Defined.

(*|
But I didn't manage to finalize the proof. There must be something
obvious I don't see. Can't someone help me with this proof?
|*)

(*|
Answer
******

There are two problems with your question. The first one is that the
statement you want to prove is false, here is a proof of a counter
example.
|*)

Lemma not_app_forward :
  not
    (forall (p p' : prog) (input1 input2 output1 output2 : list nat),
        Forward input1 output1 = Some p ->
        Forward input2 output2 = Some p' ->
        Forward (input1 ++ input2) (output1 ++ output2) = Some (p ++ p')).
Proof.
  intros abs.
  assert
    (tmp := abs (Select 1 :: Backspace :: nil) (Select 1 :: Select 2 :: nil)
                (1 :: 2 :: nil) (1 :: 2 :: nil) nil (1 :: 2 :: nil)
                refl_equal refl_equal).
  compute in tmp.
  discriminate.
Qed.

(*|
So, contrary to your claim, this is not a simple lemma.

The second problem is that the function has a complicated shape and
the proof by induction is difficult to organize. I cover this aspect
just below.

From the structure of the function ``Forward``, it is natural that you
should perform your proof by induction over the ``input`` argument,
because it is the argument where recursive calls occur on a subterm.
However the proof is made complicated by the fact that recursive calls
happen not only on direct subterms (as in ``Forward rest ...``) but
also in subterms of subterms (as in ``Forward rrest ...``).

There are several ways out of this difficulty, but all require some
amount of explanation or learning.

1. One way is to use the ``Equations`` plugin to Coq and redefine your
   ``Forward`` function using Equations. You can then use functional
   induction to solve your problem: this will use an induction
   principle that especially tailored to your problem.

2. A second way is to build a tailored induction principle by hand.
   Here is an attempt.
|*)

Definition two_step_list_induction {A : Type} :
  forall (P : list A -> Prop),
    P nil ->
    (forall a, P (a :: nil)) ->
    (forall a b tl,
        P (b :: tl) -> P tl -> P (a :: b :: tl)) ->
    forall l, P l.
Proof.
  intros P Pn P1 Prec. fix tsli 1. intros [| x l].
  - exact Pn.
  - generalize (tsli l).
    destruct l as [| y tl]; intros Pl.
    + exact (P1 x).
    + apply Prec; [assumption | exact (tsli tl)].
Defined.

(*|
   You can then start your proof with a command of the following
   shape:
|*)

Lemma app_forward :
  forall (p p' : prog) (input1 input2 output1 output2 : list nat),
    Forward input1 output1 = Some p ->
    Forward input2 output2 = Some p' ->
    Forward (input1 ++ input2) (output1 ++ output2) = Some (p ++ p').
Proof.
  intros p p' input1. revert p.
  induction input1 as [| a | a b tl Ih1 Ih2] using two_step_list_induction.
Abort. (* .none *)

(*|
   But, as I already said, the lemma you want to prove is actually
   false, so there is no way this proof will ever work and I cannot
   illustrate that the proposed approach is going to work.

   EDIT: Now that the original question has been corrected, here is a
   full correction to the original question:
|*)

Lemma app_forward : forall (p p' : prog) (input1 input2 output : list nat),
    Forward input1 output = Some p ->
    Forward input2 nil = Some p' ->
    Forward (input1 ++ input2) output = Some (p ++ p').
Proof.
  intros p p' input1. revert p.
  induction input1 as [| x | x xx rrest Ih1 Ih2] using two_step_list_induction.
  - simpl. intros p input2 [| no1 output].
    + intros [= p_is_nil]. rewrite <- p_is_nil. simpl. auto.
    + discriminate.
  - simpl.
    destruct output as [| y r]; simpl; try discriminate.
    destruct (x =? y); try discriminate.
    destruct r as [| no12 output1]; simpl; try discriminate.
    now intros [= pval] v2; rewrite <- pval, v2; simpl.
  - intros p input2 output.
    destruct output as [| y r].
    + simpl (Forward (x :: xx :: rrest) nil).
      destruct (Forward rrest nil) as [v |] eqn:vtl; try discriminate.
      intros [= pval] p'val.
      assert (tmp := Ih2 _ _ _ vtl p'val).
      simpl. rewrite tmp, <- pval. easy.
    + change (Forward (x :: xx :: rrest) (y :: r)) with
        (if x =? y then match Forward (xx :: rrest) r with
                        | Some pp => Some (Select x :: pp)
                        | None => None end
         else match Forward rrest (y :: r) with
              | Some pp => Some (Select x :: Backspace :: pp)
              | None => None
              end).
      destruct (Forward (xx :: rrest) r) as [vrest |] eqn:eqnrest.
      * destruct (x =? y) eqn:xeqy.
        -- intros [= vp ] v2. rewrite <- vp. clear vp.
           generalize (Ih1 _ _ _ eqnrest v2). simpl.
           rewrite xeqy. intros it. rewrite it. easy.
        -- destruct (Forward rrest (y :: r)) as [v |] eqn:eqnrrest;
             try discriminate.
           intros [= vp] v2. rewrite <- vp. clear vp.
           simpl. rewrite xeqy, (Ih2 _ _ _ eqnrrest v2). easy.
      * destruct (x =? y) eqn:xeqy; try discriminate.
        destruct (Forward rrest (y :: r)) as [v |] eqn:eqnrrest;
          try discriminate.
        intros [= vp] v2. rewrite <- vp. clear vp.
        simpl. rewrite xeqy, (Ih2 _ _ _ eqnrrest v2). easy.
Qed.

(*|
   A few comments on this solution:

   - The code posted in the original function contains 3 recursive
     calls, one where the argument is the immediate sublist (``rest``)
     and 2 where the argument is the second sublist (``rest``). The
     first one is handled by induction hypothesis ``Ih1`` and the
     other are handled by induction hypothesis ``Ih2``. For a reason I
     have no time to investigate, my proof needs 4 uses of induction
     hypotheses instead of 3. This means that there is probably some
     duplication.

   - Sometimes, the ``simpl`` tactic is too eager to unroll the
     recursive definition until it can no longer do anything. To
     counterbalance this bias of the ``simpl`` tactic, I had to
     perform one of the *unrolling steps* by hand, without relying on
     ``simpl``. This unrolling step is performed by the ``change``
     tactic call that appears in the middle of the script.

   - Everytime that there is a recursive call in your function, the
     result is later analyzed by a ``match`` construct. To account for
     this, the proof perform case analysis on the results of recursive
     calls and uses the ``destruct ... eqn:...`` variant of the
     ``destruct`` tactic to perform this analysis.

   - Aside from these advanced techniques, the proof is just guided by
     the interaction with Coq.

   This proof script was verified with coq-8.15 with the ``List`` and
   ``ZArith`` modules imported.

3. You can avoid constructing a tailored induction principle by
   relying on much more powerful well founded induction. This will
   give you a more general induction hypothesis, which can be used for
   a much wider set of recursive arguments (even arguments that are
   not structural subterms of the initial first list). Here is the
   full script:
|*)

Require Import Wellfounded.

Lemma app_forward2 : forall (p p' : prog) (input1 input2 output : list nat),
    Forward input1 output = Some p ->
    Forward input2 nil = Some p' ->
    Forward (input1 ++ input2) output = Some (p ++ p').
Proof.
  intros p p' input1. revert p.
  induction input1 as [input1 Ih]
                        using
                        (well_founded_ind
                           (wf_inverse_image (list nat) nat lt (@length nat) lt_wf)).
  destruct input1 as [| x [| xx rrest]] eqn:input1eq.
  - intros p input2 [| no1 output].
    + intros [= p_is_nil]. rewrite <- p_is_nil. simpl. auto.
    + discriminate.
  - simpl.
    destruct output as [| y r]; simpl; try discriminate.
    destruct (x =? y); try discriminate.
    destruct r as [| no12 output1]; simpl; try discriminate.
    now intros [= pval] v2; rewrite <- pval, v2; simpl.
  - intros p input2 output.
    assert (rrestlt : length rrest < length (x :: xx :: rrest)).
    + now simpl; auto with arith.
    + assert (restlt : length (xx :: rrest) < length (x :: xx :: rrest)).
      * now simpl; auto with arith.
      * destruct output as [| y r].
        -- simpl (Forward (x :: xx :: rrest) nil).
           destruct (Forward rrest nil) as [v |] eqn:vtl; try discriminate.
           intros [= pval] p'val.
           assert (tmp := Ih _ rrestlt _ _ _ vtl p'val).
           simpl. rewrite tmp, <- pval. easy.
        -- change (Forward (x :: xx :: rrest) (y :: r)) with
             (if x =? y then match Forward (xx :: rrest) r with
                             | Some pp => Some (Select x :: pp)
                             | None => None end
              else match Forward rrest (y :: r) with
                   | Some pp => Some (Select x :: Backspace :: pp)
                   | None => None
                   end).
           destruct (Forward (xx :: rrest) r) as [vrest |] eqn:eqnrest.
           ++ destruct (x =? y) eqn:xeqy.
              ** intros [= vp] v2. rewrite <- vp. clear vp.
                 generalize (Ih _ restlt _ _ _ eqnrest v2). simpl.
                 rewrite xeqy. intros it. rewrite it. easy.
              ** destruct (Forward rrest (y :: r)) as [v |] eqn:eqnrrest;
                   try discriminate.
                 intros [= vp] v2. rewrite <- vp. clear vp.
                 simpl. rewrite xeqy, (Ih _ rrestlt _ _ _ eqnrrest v2). easy.
           ++ destruct (x =? y) eqn:xeqy; try discriminate.
              destruct (Forward rrest (y :: r)) as [v |] eqn:eqnrrest;
                try discriminate.
              intros [= vp] v2. rewrite <- vp. clear vp. simpl.
              rewrite xeqy, (Ih _ rrestlt _ _ _ eqnrrest v2). easy.
Qed.

(*|
   A careful scrutiny of the script for lemma ``app_forward2`` shows
   that the script is almost the same as for ``app_forward``. Three
   main hints:

   - ``well_founded_induction`` combined with ``wf_inverse_image``,
     ``length`` and ``lt_wf`` gives a general induction hypothesis
     that can be use for every case where ``input1`` is replaced with
     a list that is shorter in length.

   - ``destruct input1`` replaces every instance of ``input1`` with a
     variety of cases, including the instance that appears in the
     induction hypothesis.

   - all calls to induction hypotheses ``Ih1`` and ``Ih2`` in the
     previous solution have simply been replaced by calls to ``Ih``,
     using hypotheses ``restlt`` and ``rrestlt`` to guarantee length
     decrease.
|*)
