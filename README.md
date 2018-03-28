# amen-calculator
A program to perform and display calculations with arithmetical combinators, based 
on arithmetic the arithmetic (addition, multiplication, exponentiation
and nought) of Church numerals.

You might also use the program to do your shopping, though it lacks some amenities,  
eg. convenient numerical display and input. It is more useful for
investigating algebraic laws.

These "AMEN" combinators are combinatorially complete, ie. define the same numerical functions as the
\lambda-calculus. They satisfy interesting algebraic laws, slightly weaker than the
arithmetic of the same operations on transfinite ordinals (except 1^a = 1 and 0*a = 0.)
One can take them as a basis for Turing-complete computation. 
An (bracket-)abstraction operation is defined, based on "logarithmic" ideas 
due to Boehm. 

The program evaluates arithmetical expressions built out of the 4 constants
(+),(*),(^),0 by four binary operators, by rewriting according to certain oriented
algebraic equations. Crucially, we can examine the reduction sequences, and assess
expressions for \zeta-equality. 

The program is best run from ghci. The most useful function is called "test"
that takes an expression as argument, and prints a representation of the first reduction sequence
in a certain order. The expression to be tested is assembled in a certain syntax
represented in haskell: binary operators :+:, :*:, :^:, :!: and unary constants
V"+", V"*",V"^",V"0", and variables; ghci is useful for building expressions making use of
let-expressions. A rudimentary parser from strings is also available. 

Various  combinators are defined, for example the standard combinator-sets IBCKW
and SKI (also combinatorially complete). But there are also pairing combinators and 
their projections, combinators related to currying, fixed points, the continuation
monad, and so on.  You have to browse the the code to find these.
