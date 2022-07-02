(*|
#######################################################################
How can I avoid stack overflow or segmentation fault in Coq ``nat``\ s?
#######################################################################

:Link: https://stackoverflow.com/q/13662274
|*)

(*|
Question
********

I'm currently working with `vellvm
<http://www.cis.upenn.edu/~jianzhou/Vellvm/>`__, developing a
transformation on it. I'm a Coq newbie.

While programming, I faced the following warning:

    Warning: Stack overflow or segmentation fault happens when working
    with large numbers in nat (observed threshold may vary from 5000
    to 70000 depending on your system limits and on the command
    executed).

My function that generates this warning calculates a signature. The
signature is divided in superior and inferior bits. Given two ``nat``\
s ``n1`` and ``n2`` representing the superior bits and the inferior
bits, it calculates ``(n1 * 65536) + n2`` - this is an abstraction for
put two binary numbers of 16 bits side-by-side.

I was quite surprised because Coq ``nat`` definition appears to handle
big ints from outside, thanks to the ``S`` constructor.

How should I avoid this warning/use big numbers in Coq? I'm open to
change the implementation from ``nat`` to some kind of binary
construction.
|*)

(*|
Answer
******

Instead of using the ``nat`` type in Coq, it's sometimes (when you
have to manipulate big numbers) better to use the `Z
<http://coq.inria.fr/distrib/8.4/stdlib/Coq.Numbers.BinNums.html#Z>`__
type, which is a formalization of integers using a sign magnitude pair
representation. The tradeoff is that your proofs might get slightly
more complex; ``nat`` is very simple, and so admits simple proof
principles.

However, in Coq there's an extensive use of notation to make it
simpler to write definitions, theorems, and proofs. Coq has an
extremely small kernel (we want this because we want to be able to
believe the proof checker is correct, and we can read that) with a lot
of notation on top of it. However, as there are different
representations of things, and only a few good symbols, our symbols
typically clash. To get past this, Coq uses `interpretation scopes
<http://coq.inria.fr/doc/Reference-Manual015.html>`__ to disambiguate
symbols, and resolve them into names (because ``+`` means ``add``,
``plus``, etc...).

You are correct, using ``Z_scope`` is where, ``+`` for ``plus`` within
``Z``.
|*)
