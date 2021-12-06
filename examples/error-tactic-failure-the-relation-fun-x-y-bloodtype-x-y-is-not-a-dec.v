(*|
####################################################################################################################################################
Error "Tactic failure: The relation (``fun x y : BloodType => x <> y``) is not a declared reflexive relation." when proving a theorem about function
####################################################################################################################################################

:Link: https://stackoverflow.com/questions/61134408/error-tactic-failure-the-relation-fun-x-y-bloodtype-x-y-is-not-a-dec
|*)

(*|
Question
********

I'm self studying Coq and playing with it. I wanted to try and write a
function that computes blood type based on two alleles. However, I'm
getting an error "Tactic failure: The relation (``fun x y : BloodType
=> x <> y``) is not a declared reflexive relation." when trying to
prove that any other pair of alleles but ``TypeO`` will not result
type ``TypeO`` blood.

There's three alleles:
|*)

Inductive BloodTypeAllele : Type :=
| BloodTypeA
| BloodTypeB
| BloodTypeO.

(*| And four blood types: |*)

Inductive BloodType : Type :=
| TypeA
| TypeB
| TypeAB
| TypeO.

(*| Mapping between them is as follows: |*)

Fixpoint bloodType (a b : BloodTypeAllele) : BloodType :=
  match a, b with
  | BloodTypeA, BloodTypeA => TypeA
  | BloodTypeA, BloodTypeO => TypeA
  | BloodTypeA, BloodTypeB => TypeAB
  | BloodTypeB, BloodTypeB => TypeB
  | BloodTypeB, BloodTypeA => TypeAB
  | BloodTypeB, BloodTypeO => TypeB
  | BloodTypeO, BloodTypeA => TypeA
  | BloodTypeO, BloodTypeB => TypeB
  | BloodTypeO, BloodTypeO => TypeO
  end.

(*|
I can prove that ``BloodTypeO`` and ``BloodTypeO`` results ``TypeO``
blood.
|*)

Theorem double_O_results_O_type :
  bloodType BloodTypeO BloodTypeO = TypeO.
Proof.
  reflexivity.
Qed.

(*|
But I can't prove that any other combination will not result to
``TypeO`` blood.
|*)

Theorem not_double_O_does_not_result_O_type :
  forall (b1 b2 : BloodTypeAllele),
    b1 <> BloodTypeO \/ b2 <> BloodTypeO ->
    bloodType b1 b2 <> TypeO.
Proof.
  intros b1 b2 H.
  destruct b1.
  - destruct b2.
    + simpl. Fail reflexivity. (* .fails *)

(*| Because I'm getting following error: |*)

      Fail reflexivity. (* .unfold .messages *)
Abort. (* .none *)

(*|
I tried importing the library, but the error remained the same. I'm
very new to Coq, so I'm probably looking over something very obvious.
|*)

(*|
Answer
******

One part of the problem is that you don't reason with a negated
predicate in the same way as you reason on the direct predicate. You
have to think again in terms of logic, before expecting Coq to work
for you.

Let's go back to a very basic logical inference "All humans are
mortal, Socrates is human, therefore he is mortal". If my cat is
mortal, does it mean my cat is human? No! When you work with negation,
the problem is very close to this.

Now, let's concentrate on your problem. There is a specific tactic to
help prove basic instances of equality ``reflexivity``. There is also
a specific tactic to help prove basic instances of "non-equality".
This tactic is called ``discriminate`` and it will work in your case.

Negation of equality appears in two different fashion in your
exercise. Sometimes you need to prove a negated equality that is
obvious to your naked eye and in this case, ``discriminate`` may do
the job. Sometimes, you need to prove a negated equality that is
obviously not provable (it will happen later in you exercise, I
tried). In that case, the way to progress is to discover that there is
an assumption in you goal that actually contains an inherent
contradiction, or that two hypotheses are contradictory to each other.
In that case, the solution is to try ``destruct H`` where ``H`` is the
hypothesis that is obviously wrong.

In the case of your exercise, you will also need to understand how to
cope with an ``or`` in an hypothesis, ``destruct`` will still be
relevant for that case.

I suggest you read the free document `coq in a hurry
<https://cel.archives-ouvertes.fr/inria-00001173v6/document>`__ as a
tutorial for this. In particular, it explains that for every logical
construct, the way to handle this construct is different, whether the
construct appears as the conclusion of a goal or as an hypothesis.
There is a short table to be used as a first hint list for most basic
reasoning steps.

Another piece of advice: don't use the ``Fixpoint`` command when the
function you wish to define is not recursive. In you case the function
``bloodType`` should have defined using the ``Definition`` keyword.
Using ``Fixpoint`` makes the definition uselessly complicated and this
may bite you later in your experiments.

I am excited to see you learn on your own, have fun, and ask
questions!
|*)
