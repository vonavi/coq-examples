(*|
##########################################################################
How does one inspect what more complicated tactics do in Coq step-by-step?
##########################################################################

:Link: https://stackoverflow.com/questions/54047766/how-does-one-inspect-what-more-complicated-tactics-do-in-coq-step-by-step
|*)

(*|
Question
********

I was trying to go through the famous and wonderful `software
foundations book
<https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab30>`__
but I got to an example where ``simpl.`` and ``reflexivity.`` just do
to much under the covers and are hindering my learning &
understanding.

I was going through the following theorem:
|*)

Require Import Coq.Arith.EqNat. (* .none *)
Theorem plus_1_neq_0 : forall n : nat,
    beq_nat (n + 1) 0 = false. (* n+1 != 0 *)
Proof.
  intros n. destruct n as [| n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*|
what I really want is something that allows me to go through step by
step what ``simpl.`` and ``reflexivity.`` did. Is there something that
allows me to do that?

----

Destruct is suppose to resolve the following issue:

    because the first argument to ``beq_nat`` (which is just ``not
    equal`` i.e. ``!=``) does a matching but the first input depends
    on a unknown variable ``n`` and the same thing for ``+`` so the
    matching can't do anything, so doing ``simpl.`` gets us stuck (for
    some reason).

which it clearly it must resolve it since Coq later accepts the proof.
But if one looks carefully what the second goal is, it seems that the
same issue as above is re-introduced:
|*)

Goal forall n : nat, beq_nat (n + 1) 0 = false. (* .none *)
  intros n. (* .none *) destruct n as [| n']. (* .unfold .no-in *)

(*|
now we have ``n'`` as the first argument for both ``beq_nat`` and
``+`` again. However, to a novice like me, ``simpl.`` miraculously
does work this time for some mysterious reason. I obviously read the
``simpl.`` `documentation
<https://coq.inria.fr/refman/proof-engine/tactics.html?highlight=simpl#coq:tacn.simpl>`__
but being a novice in this I didn't really know what I was looking for
and it was to dense for me to form an understanding of it that was
helpful...

Anyway, why does it work here? The reason I am asking is because it
would have never occurred to me to use destruct on this example proof,
especially cuz of the re ocurrence of ``n'`` an unknown variable, and
it seems that being able to see what really happened or what was
different would be useful. So I thought checking a step-by-step break
down of these type of things would be useful (rather than posting a
new SO question every other day).

----

Note I did see this question:

`Step by step simplification in coq?
<https://stackoverflow.com/questions/39355817/step-by-step-simplification-in-coq>`__

but I couldn't find a way to make it useful for me since it was
tailored for that particular example to much. Hopefully my question
doesn't become to narrow to my particular example, though it might
since the step by step break down might not be possible without
knowing how ``simpl.`` (or ``reflexivity.``) works already (or at
least the above answers to the question above gave me that
impression).
|*)

(*|
Answer
******

One way to break the evaluation down is to give an argument to
``simpl``, as suggested in `the question you linked
<https://stackoverflow.com/questions/39355817/step-by-step-simplification-in-coq>`__.
``simpl f`` allows to simplify only the sub-expressions that appear
under calls to ``f``. In this case, ``simpl Nat.add`` (or ``simpl
plus`` or ``simpl "+"``) simplifies ``S n' + 1`` into ``S (n' + 1)``.
Then ``simpl beq_nat`` turns ``beq_nat (S (n' + 1)) 0`` into
``false``.

As for ``reflexivity``, it can conclude if the two terms under
comparison are equal up to simplification, which means that, if I am
not mistaken, you can always replace ``simpl; reflexivity`` by just
``reflexivity``.
|*)
