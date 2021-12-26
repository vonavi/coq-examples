(*|
#######################################################
Coq: controlling ``subst`` when we have many equalities
#######################################################

:Link: https://stackoverflow.com/questions/48840457/coq-controlling-subst-when-we-have-many-equalities
|*)

(*|
Question
********

If one has *many* hypothesis of the form ``a = b`` (I find that this
happens often when we use ``inversion``), is there some way to
*prevent* a substitution from happening?

I often have ``Hypothesis`` that look like

.. code::

    H0: rec = someLargeRecord { field := val1; ...; fieldn := valn }
    rel1: some_relation rec rec'
    rel2: some_relation rec rec''
    equal1: a = b
    equal2: b = c
    ...
    equal3: y = z

On running ``subst`` at this point, ``rel1``, ``rel2`` and the like
blow up, become something of the form

.. code::

    rel1: some_relation someLargeRecord { field := val1; ...; fieldn := valn } rel'
    rel2: some_relation someLargeRecord { field := val1; ...; fieldn := valn } rel''

This is horrible to work with.

I wish to somehow control ``subst``, preferably to ask it to not
consider ``H0``. Is this at all possible?
|*)

(*|
Answer
******

You can tell ``subst`` what variables to substitute. For instance, the
call

.. code-block:: coq

    subst a b y.

would substitute ``a``, ``b`` and ``c``, but not ``rec``. This might
not be convenient if you are trying to substitute several variables;
in this case, you can put the equation that you want to keep back into
the goal before calling ``subst``. For example, the following snippet
would substitute every variable in your context except for ``rec``.

.. code-block:: coq

    revert H0.
    subst.
    intros H0.
|*)
