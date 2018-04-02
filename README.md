# amen-calculator #
A program to perform and display calculations with arithmetical combinators, based 
on the arithmetic (addition, multiplication, exponentiation
and nought) of Church numerals.

You might also use the program to do your shopping, though it lacks
some amenities, (:-) 
eg. convenient numerical display and input. It is more useful for
investigating algebraic laws.

These "AMEN" combinators are combinatorially complete, ie. define the same numerical functions as the
\lambda-calculus. They satisfy interesting algebraic laws, slightly weaker than the
arithmetic of the same operations on transfinite ordinals (except 1^a = 1 and 0*a = 0.)
One can take them as a basis for Turing-complete computation. 
A (bracket-)abstraction operation is defined, based on "logarithmic" ideas 
due to Boehm. 

The program evaluates arithmetical expressions built out of the 4 constants
(+),(*),(^),0 by four corresponding binary operators, by rewriting
according to computationally oriented
algebraic equations. Crucially, we can examine the reduction sequences, and assess
expressions for \zeta-equality. 

The program is best run from ghci, as in

>  $ ghci amen-calulator/arithmetic-code.lhs

The most useful function is called `test`. It
takes an expression as argument, and prints a representation of its first reduction sequence
in a certain order. The expression to be tested can be assembled in
the syntax:

* binary infix operators `:+:, :*:, :^:, :<>:`,

* unary constants `V"+", V"*", V"^", V"0"`, and

* variables `va, vb, ...`, given by alphabetical strings.

In ghci one can build up expressions making use of
let-expressions. A rudimentary parser from strings is also available.
Something like


>   let (e,res):_ = prun expression (tokens "eg ^ (eggs + bacon)")
>   in test $ vb :^: va :^: blog "eg" e


should either

* complain of a parse error, or

* construct the indicated expression
  (using Boehm's logarithm inbuilt as `blog`)
  and display its most sensible reduction sequence.

Various  combinators are defined, for example the standard combinator-sets **IBCKW**
and **SKI** (also combinatorially complete). But there are also
combinators for pairing, currying, and 
projection, combinators related to currying, permutation of
arguments, fixed points, the continuation monad, and lots more.
You have to browse the the code to find these.
