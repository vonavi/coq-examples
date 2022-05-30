(*|
###############################################################
How do we know all Coq constructors are injective and disjoint?
###############################################################

:Link: https://stackoverflow.com/q/32662889
|*)

(*|
Question
********

According to `this course
<http://www.cis.upenn.edu/~bcpierce/sf/current/MoreCoq.html>`__, all
constructors (for inductive types) are injective and disjoint:

    ...Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal. For lists, the ``cons`` constructor
    is injective and ``nil`` is different from every non-empty list.
    For booleans, ``true`` and ``false`` are unequal.

(And the ``inversion`` tactic based on this assumption)

I am just wondering how do we know this assumption holds?

How do we know that, e.g., we cannot define natural numbers based on

1) a "Successor" and maybe a "Double" constructor like this:

   .. coq::
|*)

Inductive num : Type :=
| O : num
| S : num -> num
| D : num -> num.

(*|
   and

2) some ``plus`` function so that one number ``2`` can be reached via
   two different sequences/routes of constructors, ``S (S O)`` and ``D
   (S O)``?

What's the mechanism in Coq that ensures the above will never happen?

P.S. I am not suggesting the above ``num`` example is possible. I am
just wondering what makes it impossible.
|*)

(*|
Answer
******

When you define an inductive data type in Coq, you are essentially
defining a *tree* type. Each constructor gives a kind of node that is
allowed to occur in your tree, and its arguments determine the
children and elements that that node can have. Finally, functions
defined on inductive types (with the ``match`` clause) can check the
constructors that were used to produce a value of that type in
*arbitrary* ways. This makes Coq constructors very different from
constructors you see in an OO language, for instance. An object
constructor is implemented as a regular function that initializes a
value of a given type; Coq constructors, on the other hand, are
enumerating the possible values that the *representation* of our type
allows. To understand this difference better, we can compare the
different functions we can define on an object in a traditional OO
language, and on an element of an inductive type in Coq. Let's use
your ``num`` type as an example. Here's an object-oriented definition:

.. code-block:: java

    class Num {
        int val;

        private Num(int v) {
            this.val = v;
        }

        /* These are the three "constructors", even though they
           wouldn't correspond to what is called a "constructor" in
           Java, for instance */

        public static zero() {
            return new Num(0);
        }

        public static succ(Num n) {
            return new Num(n.val + 1);
        }

        public static doub(Num n) {
            return new Num(2 * n.val);
        }
    }

And here's a definition in Coq:
|*)

Reset Initial. (* .none *)
Inductive num : Type :=
| zero : num
| succ : num -> num
| doub : num -> num.

(*|
In the OO example, when we write a function that takes a ``Num``
argument, there's no way of knowing which "constructor" was used to
produce that value, because this information is not stored in the
``val`` field. In particular ``Num.doub(Num.succ(Num.zero()))`` and
``Num.succ(Num.succ(Num.zero()))`` would be equal values.

In the Coq example, on the other hand, things change, because we *can*
determine which constructor was used to form a ``num`` value, thanks
to the ``match`` statement. For instance, using Coq strings, we could
write a function like this:
|*)

Require Import Coq.Strings.String.

Open Scope string_scope.

Definition cons_name (n : num) : string :=
  match n with
  | zero   => "zero"
  | succ _ => "succ"
  | doub _ => "doub"
  end.

(*|
In particular, even though your intended meaning for the constructors
implies that ``succ (succ zero)`` and ``doub (succ zero)`` should be
"morally" equal, we can distinguish them by applying the ``cons_name``
function to them:
|*)

Compute cons_name (doub (succ zero)). (* .unfold *)
Compute cons_name (succ (succ zero)). (* .unfold *)

(*|
As a matter of fact, we can use ``match`` to distinguish between
``succ`` and ``doub`` in *arbitrary* ways:

.. code-block:: coq

    match n with
    | zero   => false
    | succ _ => false
    | doub _ => true
    end.

Now, ``a = b`` in Coq means that there is no possible way we can
distinguish between ``a`` and ``b``. The above examples show why
``doub (succ zero)`` and ``succ (succ zero)`` cannot be equal, because
we can write functions that don't respect the meaning that we had in
mind when we wrote that type.

This explains why constructors are disjoint. That they are injective
is actually also a consequence of pattern-matching. For instance,
suppose that we wanted to prove the following statement:
|*)

Goal forall n m, succ n = succ m -> n = m.

(*| We can begin the proof with |*)

  intros n m H.

(*| Leading us to |*)

  Show. (* .unfold .messages *)

(*| Notice that this goal is by simplification equivalent to |*)

  change (match succ n with
          | succ n' => n' = m
          | _       => True
          end). (* .none *)
  Show. (* .unfold .messages *)

(*| If we do ``rewrite H``, we obtain |*)

  rewrite H. (* .none *)
  change (match succ m with
          | succ n' => n' = m
          | _       => True
          end). (* .none *)
  Show. (* .unfold .messages *)

(*| which simplifies to |*)

  simpl. (* .none *) Show. (* .unfold .messages *)

(*|
At this point, we can conclude with ``reflexivity``. This technique is
quite general, and is actually at the core of what ``inversion`` does.
|*)
