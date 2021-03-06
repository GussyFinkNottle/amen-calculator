\documentclass{article}
\usepackage{hyperref}
%include polycode.fmt
%lhs2TeX.fmt
%format :^: = ":\!\wedge\hspace{-0.5ex}:\mbox{}" 
%format :*: = ":\!\times\hspace{-0.5ex}:\mbox{}" 
%format :+: = ":\!+\hspace{-0.5ex}:\mbox{}" 
%format ^ = "\wedge"
%format * = "\times"
%format ~ = "\sim"
%format <> = "\!\mathop{{}^{{}^{\cdot}}}\!"
%format :~: = ":" ~ ":"

\newcommand{\ZERO}{\!\mathop{{}^{{}^{\cdot}}}\!}


\title{The AMEN calculator}
\newcommand{\ie}{\textit{ie.\hspace{0.5ex}}}
\newcommand{\eg}{\textit{eg.\hspace{0.5ex}}}
\newcommand{\etc}{\textit{\&{}co.\hspace{0.5ex}}}
\newcommand{\logarythm}{$\lambda$og$_a$rhythm}

\begin{document}
\maketitle
\tableofcontents

\section{Benedictus benedicat}
Some haskell boilerplate. We are going to play around with
the ordinary arithmetical symbols, and versions of these
symbols in angle-brackets eg. |<+>|.

\begin{code} 
module Arithmetic where 
import Data.Char
import Prelude hiding 
               ((*),(^),(+),(<>),(&),(~)
               ,(<*>),(<^>),(<+>),(<<>>),(<&>),(<~>)
               ,(:^:),(:*:),(:+:),(:<>:),(:&:),(:~:)
               ,pi
               )
import Control.Applicative hiding ((<*>),empty) 

infixr 8  ^   
infixr 7  *   
infixr 6  +   
infixr 9  <>
infix 3   &
-- infix 3   ~  -- some weirdess about ~ as a symbol

help :: IO ()        -- Do something with this later.
help =  let eg = " test $ vc :^: vb :^: va :^: cC " ; q = '"'
        in putStrLn
             ("Load in ghci and type something like: " ++ (q:eg) ++ [q])
\end{code}

\section{Real-world arithmetical combinators}

Here are some simple definitions of binary operations corresponding to the 
arithmetical combinators: 
\begin{code}
a ^ b  = b a
a * b  = \c -> (c ^ a) ^ b
a + b  = \c -> (c ^ a) * (c ^ b)
a `naught` b = b
-- some experiments
a & b  = \c -> c a b
a ~ b  = \c -> a c b  -- |(a ~)| is a binary function with its arguments flipped. 
\end{code}

Instead of |naught|, one can use the infix operator |(<>)|, that looks
a little like a `|0|'. It discards its left argument, and returns its right. 


The type-schemes inferred for the definitions are as follows:
\begin{code}
(^)      :: a -> (a -> b) -> b
(*)      :: (a -> b) -> (b -> c) -> a -> c
(+)      :: (a -> b -> c) -> (a -> c -> d) -> a -> b -> d
(<>)     :: a -> b -> b
one      :: a -> a
-- a couple of experiments
(&)      :: a -> b -> (a -> b -> c) -> c
-- Following type declaration causes a parse error...
-- |(~)      :: (a -> b -> c) -> b -> a -> c|
\end{code}
Anyone should think:
\begin{itemize}
\item continuation transform unit
\item action of contravariant functor |_ -> c| on morphisms
\item lifted version of the above
\item |const id|
\item |id|
\item pairing
\item flip
\end{itemize}

Here are the first few numbers
\begin{code}
(<>) = naught
zero = naught
one  = zero ^ zero
suc n s =  n s * s
two  = suc one 
three = suc two
four = two ^ two
five = two + three 
six  = two * three
seven = four + three
eight = two ^ three
nine = three ^ two
ten  = two * five
\end{code}

Here they are in a list, with a common type.
\begin{code}
ff , nos :: [(a -> a) -> a -> a]
ff = [ zero,one,two,three,four
     , five,six,seven,eight,nine,ten]
nos = zero: [ suc x | x <- nos]
\end{code}


\subsection{Infinitary operations: streams and lists}
For infinitary operations (this may come later) I might need
a few things.

The first folds a binary operation (such as addition)
over the finite prefixes of a stream. So |(x1,x2,x3, ... )|
is sent to |(0, x1, x1 + x2, x1 + x2 + x3, ... )|.
\begin{code}
pfs :: (a -> a -> a) -> a -> [a] -> [a]
pfs op ze xs = pfs' xs id
               where pfs' (x:xs) b = b ze : pfs' xs (b . (op x))
\end{code}
|pfs| is applied only to streams, and returns a stream.
Think of it is a stream of finite lists, namely the list of finite
prefixes of the argumenty stream. Then we fold an operation over each list, starting
with a constant. 

\begin{code}
type Endo x = x -> x
type N x = Endo (Endo x)
index :: N [a] -> [a] -> a
index n         = (tail ^ n) * head   -- head . n tail
-- note index 0 is head

sigma :: Endo [a -> Endo b] 
pi :: Endo [ Endo a ] 
pi    = pfs (*) one
sigma = pfs (+) zero

\end{code}

Stuff related to continuations.
Should make monad instance etc.
\begin{code}
type C y x = (x -> y) -> y
ret :: x -> C y x
ret = (^)
mu  :: C y (C y x) -> C y x 
-- mu mm k = mm (ret k)
-- mu mm   = ret * mm
mu      = (^) ^ (*)    -- ((^) * (^)) ^ flip 
mp :: (a -> b) -> C y a -> C y b
mp =  (*) * (*)
{- The types |x -> C x x| and |N x| are isomorphic. -}
{- The same combinator is used in both inverse directions! -}
myflip :: (x -> C x x) -> N x
myflip = flip 
myflip' :: N x -> x -> C x x
myflip' = flip 
\end{code}

I can't remember why I thought the below was interesting.
The argument of mydrop is a Church numeral.
\begin{code}
-- any of the following type statements will do
mydrop :: C y (Endo [a]) 
-- | mydrop :: (([a] -> [a]) -> t) -> t  |
-- | mydrop :: (Endo [a] -> t) -> t  |
-- | mydrop :: N [a] -> Endo [a]  |
mydrop n  = n tail
mydrop'   = ($ tail)
\end{code}


\subsection{Booleans}

I wanted to look at Church encoding of booleans.
The following can all be restricted in such a way
that |a|, |b| and |c| are the same.  This is analogous to
the situation with Church numerals.
\begin{code}
type I2 a b c = a -> b -> c
impB  ::  I2 (I2 a b c) (I2 b d a) (I2 b d c)
orB   ::  I2 (I2 a b c) (I2 a d b) (I2 a d c)
andB  ::  I2 (I2 a b c) (I2 d b a) (I2 d b c)
posB  ::  I2 a b a
nilB  ::  I2 a b b
impB  a b p n  =  a (b p n) p
orB   a b p n  =  a p (b p n)  -- the same as numerical addition b + a
andB  a b p n  =  a (b p n) n
posB  =  const 
nilB  =  zero
if0   :: I2 a b c -> I2 b a c 
ifP   :: a        -> a
ifP   =  id 
if0   =  flip
\end{code}

\section{Syntax for arithmetical expressions}


Arithmetical expressions are constructed using a signature with 4 binary operators,
and 4 constants. 
\begin{itemize}
\item 4 constants |(^)|, |(*)|, |(+)| and |(<>)|
\item 4 binary operators |_^_|, |_*_|, |_+_| and |_<>_|
\end{itemize}

There is also an unlimited supply of fresh variables, named by strings (usually singleton characters).
An expression in which a variable occurs is said to be open, otherwise closed.

The defining equations for the arithmetical combinators generate two equivalence relations between
expressions. The first is `intensional': this is the least equivalence relation
extending the definitions, congruent to all operators in the signature.  
This means that equations between open terms can be proved by
substituting equals for equals.

The second (more useful) equivalence relation identifies more expressions.
One can also allow instances of the so-called `$\zeta$-rule' in proving equations.
\begin{center}
    \begin{tabular}{c} |x ^ a = x ^ b|  $\mbox{}\Longrightarrow\mbox{}$ |a = b| \end{tabular}
\end{center}
with the side condition that |x| is fresh to both |a| and |b|.

The $\zeta$-rule is a cancellation law. It expresses
`exponentiality':
two expressions that behave the same as exponents of a generic base
(as it were, a cardboard-cutout of a base) are equivalent. 
I call this equivalence relation $\zeta$-equality.  Any equation herein 
should be interpreted as a $\zeta$-equation, unless I explicitly say otherwise.

It may be that to determine the behaviour of an expression as an
exponent, we have to supply it with more than one base-variable.
Sometimes, `extra' variables play a role in allowing computations
to proceed, though subsequently these `extras' can be cancelled.
  
\section{Evaluating arithmetical expressions}

The arithmetical combinators are rather fascinating, but it is
easy to make mistakes when performing calculations.
We now write some code to explore on the computer
the evaluation of arithmetical expressions, built out
of our four/eight combinators.

First, here is a datatype |E| for arithmetical expressions.  The symbols 
for the constructors are chosen to suggest their interpretation as
combinators.

\begin{code}
infixr 9  :<>:
infixr 8  :^: 
infixr 7  :*:
infixr 6  :+:
infixr 5  :&:
infixr 5  :~: 
\end{code}

\begin{code}
data E  = V String
          | C String        -- experiment
          | E :^: E
          | E :*: E
          | E :+: E
          | E :<>: E        -- indirection 
          | E :~: E         -- flip (experiment)
          | E :&: E         -- pairing (experiment)
          deriving  (Eq) -- (Show,Eq) 
\end{code}

We can think of these expressions as fancy Lisp S-expressions, with four
different binary `cons' operations, each with an distinct arithmetical flavour.

As for the experiments, we can define |&| and |~| by
\begin{spec}
   (a  ~  b)  =  a      *  (b ^)
   (a  &  b)  =  (a ^)  *  (b ^)
\end{spec}

It is convenient to have atomic constants/combinators identified by symbolic strings.
The constants |"+"|, |"*"|, |"^"|, |"0"|, |"1"| (among others) are treated specially.
\begin{code}
( cA, cM, cE, cN)        
  =  ( V"+", V"*", V"^", V"0")
cI = cN :^: cN
( c0, c1 ) = (cN, V "1")
\end{code}
It is convenient to have symbols for the flipped versions:
\begin{code}
( cAcC, cMcC, cEcC, cNcC) =
  let f = ('~':) * V        -- this is typeset very wierdly
  in  ( f "+", f "*", f "^" , f "0" ) 
cB_possible      = cMcC
cK_possible      = cNcC
cI_possible      = cEcC
\end{code}

\iffalse
%    ,  V"<>"             -- discard left-hand argument
%--  cC,      cCcC,
%--  cPair , cPaircC,
%--    , V"~" , V "~~"   -- flip ;  rotR a b c - b c a  (store)
%--    , V"&" , V $~&"   -- rotL. reverse exchanges 1 and 3. 
\fi

Now we turn to evaluation of expressions. Of course, this will be
only a partial function, as there are expressions which one
cannot be completely evaluated.

To begin with, we disregard reduction sequences, and focus on
the value returned by a terminated sequence. (We'll consider reduction sequences in a moment.)

For each binary arithmetical operator, we define a function that takes two
arguments, and (sometimes) returns a `normal' form of the expression 
formed with that operator.  Then we recurse (in |eval|) over the structure of an expression
to define the code that might return its normal form.

I'm not entirely confident the following works properly.
It should match the |tlr| given later. 
\begin{code}
infixr 9  <<>>
infixr 8  <^> 
infixr 7  <*>
infixr 6  <+>
\end{code}
\begin{spec}
infixr 5  <&>     -- oh... I doubt |<,>| is available...
infixl 4  <~>
\end{spec}

\begin{code}
(<+>),(<*>),(<^>),(<<>>) :: E -> E -> E

a <+> b = case a of
          V"0"         ->  b
          _            ->  case b of
                           V"0"           ->  a
                           b1 :+: b2      ->  (a <+> b1) <+> b2
                           _              ->  a :+: b 
a <*> b = case a of
          V"1"         ->  b
          _ :^: V"0"   ->  b
          _            ->  case b of
                           V"0"           ->  b
                           b1 :+: b2      ->  (a <*> b1) <+> (a <*> b2)
                           b1 :*: b2      ->  (a <*> b1) <*> b2
                           V"1"           ->  a
                           V"0" :^: V"+"  ->  a
                           V"1" :^: V"*"  ->  a
                           _    :^: V"0"  ->  a
                           _              ->  a :*: b 
a <^> b = case b of
          V"0"           ->  V"1"  -- b :^: b
          V"1"           ->  a
          b1 :+: b2      ->  (a <^> b1) <*> (a <^> b2)
          b1 :*: b2      ->  (a <^> b1) <^> b2
          V"0" :^: V"+"  ->  a
          V"1" :^: V"*"  ->  a
          _  :^: V"0"    ->  a
          b1 :^: V"^"    ->  b1 <^> a   -- note: destroys termination
          b1 :^: V"*"    ->  case b1 of { V"1" -> a ; _ :^: V"0" -> a ; _ -> b1 <*> a}
          b1 :^: V"+"    ->  case b1 of { V"0" -> a ; _ -> b1 <+> a}
          b1 :^: b2      ->  a :^: (b1 <^> b2) 
          _              ->  a :^: b 
_ <<>> b = b

\end{code}

The following (partial!) function then evaluates an arithmetic
expression.

\begin{code}
eval :: E -> E
eval a   = case a of  b1 :+: b2    -> eval b1 <+> eval b2
                      b1 :*: b2    -> eval b1 <*> eval b2
                      b1 :^: b2    -> eval b1 <^> eval b2
                      _ :<>: b2    -> eval b2
                      _            -> a 
\end{code}


This first piece of code is an evaluator, that computes the normal form
of an expression (with respect to some rewriting rules hard-wired in the code),
unless it "hangs", or consumes all the memory in your computer.)
Such an evaluator may let look at the normal form of an expression, if it has one.
but it doesn't show how this was arrived at. (This is done below.)

There are various systems and reduction strategies of interest.  They
arise from the algebraic structure: the additive and multiplicative
monoids, weak distributivity, etc.


\section{Rewriting arithmetical expressions}

If an expression does not have a value, then the |eval| function
of the last section will not produce one, thank heavens.  Nevertheless, one
may want to observe finite segments of the sequence of reductions.  
The second piece of code is for watching the reduction
rules in action.

The machinery is controlled by a single (case-)table of
contractions (ie. top-level reductions), in the function |tlr| below.
This maps an expression to the list of expressions to which it
can be reduced in one top-level step (rewriting the root of the expression).  
To vary the details of reduction, one can tinker with the definition
of |tlr|.  

Although the lists returned here are at most singletons, in other variants
there might be overlap: more than one reduction rule might apply.  In such a case,
the order of pattern matching might matter.
\begin{code}
tlr :: E -> [E]
tlr e = case e of 
          -- addition |+|
             (a :+: (b :+: c))    ->  [ (a :+: b) :+: c          ]  --  space reuse
             (V "0" :+: a)        ->  [ a                        ]  --  drop1
             (a :+: V "0")        ->  [ a                        ]  --  drop1
          -- multiplication |*|
             (a :*: (b :+: c))    ->  [ (a :*: b) :+: (a :*: c)  ]  --  2 to 3
             (a :*: V "0")        ->  [ c0                       ]  --  drop1
             (a :*: (b :*: c))    ->  [ (a :*: b) :*: c          ]  --  reuse
             (a :*: V "1")        ->  [ a                        ]  --  drop1
             (V "1" :*: a)        ->  [ a                        ]  --  drop1
          -- random |*| optimisations
             (V "*" :*: (V "^" :^: V "*"))  -> [ V "~" ]  -- EXPERIMENT!!
             ((a :*: V "*") :*: (V "^" :^: V "*"))  -> [ a :*: V "~" ]  -- EXPERIMENT!! re reassociate
             (V "~" :*: V "~")    ->  [ c1                       ]  -- missing a square root, I think
             (V "^" :*: V "~")    ->  [ V "&"                    ]  -- apparently. 
             (V "&" :*: V "~")    ->  [ V "^"                    ]  -- apparently. Others?
          --
          -- exponentiation |^|
             (a :^: (b :+: c))    ->  [ (a :^: b) :*: (a :^: c)  ]  --  2 to 3
             (a :^: V "0")        ->  [ c1                       ]  --  drop1
             (a :^: (b :*: c))    ->  [ (a :^: b) :^: c          ]  --  reuse
             (a :^: V "1")        ->  [ a                        ]  --  drop1   -- idle
          -- random |^| optimisations 
             (V "^" :^: V "~")    ->  [ c1                       ]  -- strong eta
             (V "0" :^: V "+")    ->  [ c1                       ]  -- |0/1| left units for |+/*|
             (V "1" :^: V "*")    ->  [ c1                       ]
          -- 
             (a :^: b :^: V "+")  ->  [ b :+: a                  ]  --  drop1
             (a :^: b :^: V "*")  ->  [ b :*: a                  ]  --  drop1
             (a :^: b :^: V "^")  ->  [ b :^: a                  ]  --  drop1   -- top 2 swap
             (a :^: b :^: V "0")  ->  [ b :<>: a                 ]  --  drop1   -- indirection
             (a :^: b :^: V "~")  ->  [ b :~: a                  ]  -- 
             (a :^: b :^: V "&")  ->  [ b :&: a                  ]  -- 

             (a :^: b :^: V "~+")  ->  [ a :+: b                  ]  --  drop1
             (a :^: b :^: V "~*")  ->  [ a :*: b                  ]  --  drop1
             (a :^: b :^: V "~^")  ->  [ a :^: b                  ]  --  drop1   -- top 2 swap
             (a :^: b :^: V "~0")  ->  [ a :<>: b                 ]  --  drop1   -- indirection
             (a :^: b :^: V "~~")  ->  [ a :~: b                  ]  -- 
             (a :^: b :^: V "~&")  ->  [ a :&: b                  ]  -- 

             (a :^: (b :&: c))    ->  [ c :^: b :^: a            ]  -- a 2-chain 
             (a :^: (b :~: c))    ->  [ c :^: a :^: b            ]  -- a 3-chain 
          -- naught
             (_ :<>: b)           ->  [ b                        ]  --  drop1
          -- nothing else is reducible
             _                    ->  [                          ]
\end{code}

Thought: the associativity laws can be done in place.
The distribution laws cannot. Quite a few others can reuse the
redex as an indirection node.

To represent subexpressions, we use a `zipper', in a form in which the
context of a subexpression is represented by a linear function.  We
represent each part |e| of an expression |e'| (at a particular
position) as a pair |(f,e)| consisting of the subexpression |e| there,
and a linear function |f| such that |f e = e'|.  (By construction, the
function is linear in the sense that it uses its argument exactly
once.) Intuitively you `plug' the subexpression |e| into the `context'
|f| to get back |e'|.

The function |sites| returns (in top down preorder: root, right, left \ldots) 
all the subexpressions of a given expression, together with the 
one-hole contexts in which they occur.  This includes the improper case of
the expression itself in the empty context. I represent the one-hole contexts
by a composition of functions that when applied to the contextualised part
will return the outermost expression.
\begin{code}
sites :: E -> [(E->E,E)]
sites e  =  (id,e) : case e of
                       (a :+: b)   ->  h (:+:) a b
                       (a :*: b)   ->  h (:*:) a b
                       (a :^: b)   ->  h (:^:) a b
                       (a :&: b)   ->  h (:&:) a b
                       (a :~: b)   ->  h (:~:) a b 
                       (a :<>: b)  ->  sites b          -- DANGER! indirection
                       _           ->  []               -- no internal sites
            where
              h o a b   =  i ++ ii where
                              i   =  [ ((a `o`) . f,p) | (f,p) <- sites b ]  -- right operand b first
                              ii  =  [ ((`o` b) . f,p) | (f,p) <- sites a ]
\end{code}
A variant. %| sites e = [ (composelist fs,p) | (fs,p) <- sites' e ] |

\begin{code}
-- sites' :: E -> [([E->E],E)]
sites' e  =  ([],e) : case e of
                       (a :+: b)   ->  h cA a b
                       (a :*: b)   ->  h cM a b
                       (a :^: b)   ->  h cE a b
                       (a :&: b)   ->  h cPair a b
                       (a :~: b)   ->  h cC a b 
                       (a :<>: b)  ->  sites' b          -- DANGER! indirection
                       _           ->  []                -- no internal sites
            where
              h o a b   =  i ++ ii
                           where
                              i   =  [ ((a :^: o) : f,p) | (f,p) <- sites' b ]  -- right operand b first
                              ii  =  [ ((b :^: o :^: cC) : f,p) | (f,p) <- sites' a ]
\end{code}

Quick hack towards linear logs.
\begin{code}
lblog vn e = head [foldr (:*:) c1 (reverse fs) | (fs,p) <- sites' e, p == V vn] 
\end{code}
It should be noted that `far-right' sites are prioritised. This mirrors the 
normal situation, where the left comes first.

A criticism of the above code is that it might be more useful to
keep a \emph{list} of off-path expressions (rather than the
composite of functions like |(o a)| and |(flip o a)|). In
a linear logarithm, we want to replace composition with
multiplication.

Now we define for any expression a list of the expressions to which it
reduces in a single, possibly internal step, at exactly one site 
in the expression.  This uses the function |tlr| to get
top-level reducts. 

\begin{code}
reducts :: E -> [ E ]
reducts a     = [ f a'' | (f,a') <- sites a, a'' <- tlr a' ]
\end{code}

\subsection{The tree of reduction sequences, and access to it}

We need a structure to hold the reduction sequences from an
expression.  So-called `rose' trees, with nodes labelled with
expressions seem ideal.

\begin{code}
data Tree a = Node a [ Tree a ] deriving Show
\end{code}

We define a function which maps an expression to its tree of 
reduction sequences.

\begin{code}
reductTree :: E -> Tree E
reductTree e = Node e [ reductTree e' | e' <- reducts e ]
\end{code}

The following function maps a tree to
a sequence enumerating the nonempty sequences of
node labels encountered on a path from the root of the tree to a (leaf) node without descendants.
\begin{code}
branches :: Tree a -> [[a]]
branches (Node a []) = [ [a] ]
branches (Node a ts) = [ a : b | t <- ts, b <- branches t]
\end{code}

Putting things together, we can map an expression to 
a sequence of its reduction sequences. (Hence |rss|.)
\begin{code}
rss :: E -> [[E]]
rss = branches . reductTree
\end{code}

The first `canonical' reduction sequence in my enumeration seems
top-down, or lazy in some sense.  It is usually
quite usable (to understand what is going on in a calculation),
at least by me.



\section{B{\"o}hm's \logarythm} 

This code constructs the \logarythm{} of an expression
with respect to a variable name. 

B{\"o}hm's combinators. Check carefully!!
\begin{code}
cBohmA a b   = let curry  g = cPair :+: g :^: cK in        -- additive
               let curry' g = cPair :*: cM :*: (g :^: cE)  -- multiplicative
               in curry' (a :^: cE :+: b :^: cE)
cBohmE  a b  = a :*: cPair :+: b :*: cE
cBohmE' a b  = b :*: cC :+: a :*: cE
cBohmM  a b  = a :+: b
cBohm0  a    = c0 :~: a
cBohm0' a    = c0 :*: (a :^: cE)
cBohmC  a b  = a :+: b :*: cE          -- I had cC instead of cE!
cBohmP  a b  = a :*: cE :+: b :*: cE   -- pairing
\end{code}
These have the crucial properties
\begin{spec}
   x ^ cBohmA a b  = (x ^ a) + (x ^ b)
   x ^ cBohmM a b  = (x ^ a) * (x ^ b)
   x ^ cBohmE a b  = (x ^ a) ^ x ^ b
   x ^ cBohm0 a    = a
   x ^ cBohmP a b  = ( x ^ a  ,  x ^ b )
   x ^ cBohmC a b  = ( x ^ a  ~  x ^ b )
\end{spec}
used in defining the logarithm.

The code below can perhaps refined to keep the size
of its logarithms down.  It is very naive.
The interesting cases are those where
the variable occurs in just once of a pair of operands.


I am about to change this, so I'll try to clarify my thoughts.
I intend to treat \emph{linear} logarithms explicitly as a special case.
With linear logarithms, when searching for the single
occurrence of the variable, we accumulate a list of functions $[f_1, \dots f_n]$,
the composition of which (in one direction or another) is a function that sends an given expression
to the top-level expression with the variable occurrence replaced by an occurrence of the given expression.
The logarithm in this case is a certain product.
The functions are left or right sections of a binary operator:
| (a `o`)| or |(`o` a)| -- which can be written | (`~o` a)|,
if |`~o`| is the flipped version of |`o`|.
Now we form the linear log as the product
\[
  f_1^{o_1} \times \ldots \times f_n^{o_n}
\]
\begin{code}
blog v e | not (v `elem` fvs e) = cBohm0 e 
blog v e =
     case e of 
          a :+: b -> case (v `elem` fvs a,v `elem` fvs b) of
                        (False,True)    -> (blog v b) :*: (a :^: cA)
                        (True,False)    -> (blog v a) :*: (b :^: cA :^: cC)
                        _               -> cBohmA (blog v a) (blog v b) 
          a :*: b -> case (v `elem` fvs a, v `elem` fvs b) of
                        (False,True)    -> (blog v b) :*: (a :^: cM)
                        (True,False)    -> (blog v a) :*: (b :^: cB)
                        _               -> cBohmM (blog v a) (blog v b)
          a :^: b -> case (v `elem` fvs a, v `elem` fvs b) of
                        (False,True) -> case b of
                                         V v  -> a :^: cE
                                         _    -> blog v b :*: (a :^: cE)
                        (True,False) -> case a of
                                         V v  -> b
                                         _    -> blog v a :*: b
                        _            -> cBohmE' (blog v a) (blog v b)
          a :~: b -> cBohmC (blog v a) (blog v b)
          a :&: b -> cBohmP (blog v a) (blog v b)
          V nm     -> if nm == v then c1 else cBohm0 e
\end{code}
\iffalse
{-
\begin{spec}
     let 
         x =  [(f,t) | (f,t) <- sites e, t == V v ]
     in case x of
           [(f,t)] -> -- single occurrence
           []      -> -- does not occur
           _       -> -- multiple occurrences
\end{spec}
-}         
\fi
The following function returns a list of all the variable names occurring in an expression.
The list is returned in the order in which variables are encountered in a depth-first scan.
\begin{code}
fvs e = nodups $ f e []
               where f (V nm) = if nm `elem` [ "0", "1", "^", "*", "+",
                                               "$", ",", "~", ".", "&" ]
                                then id else (nm:)
                                -- NB: |,| is just |&| (pairing).
                                --     |.| is reverse |*| (unused)
                                --     |$| is reverse |^| (unused)
                     f (a :^: b)   = f a . f b 
                     f (a :*: b)   = f a . f b 
                     f (a :+: b)   = f a . f b
                     f (a :<>: b)  = f b  -- we regard position a as junk
                     f (a :~: b)   = f a . f b
                     f (a :&: b)   = f a . f b
\end{code}
It has to be said that `$x$ occurs in $a$' is merely a sufficient, but not
a necessary condition for $a$ to be independent of $x$. Consider | vx :^: c0 |.


\appendix

\section{Bureaucracy and gadgetry}

To save typing, names for all single-letter variables
\begin{code}
( va, vb, vc, vd,  ve, vf, vg, vh,
  vi, vj, vk, vl,  vm, vn, vo, vp,
  vq, vr, vs, vt,  vu, vv, vw, vx, vy, vz) 
  = ( V"a", V"b", V"c", V"d",      V"e", V"f", V"g", V"h",
      V"i", V"j", V"k", V"l",      V"m", V"n", V"o", V"p",
      V"q", V"r", V"s", V"t",      V"u", V"v", V"w", V"x", V"y", V"z")
\end{code}

We code a few useful numbers as expressions.
\begin{code}
c2, c3, c4 , c5, c6, c7, c8, c9, c10 :: E
(c2,c3,c4)   = (c1 :+: c1,  c2 :+: c1,  c2 :^: c2)
(c5,c6,c7)   = (c3 :+: c2,  c3 :*: c2,  c3 :+: c4)
(c8,c9,c10)  = (c2 :^: c3,  c3 :^: c2,  c2 :*: c5)
\end{code}
|c0| and |c1| have already been defined.

It is time we had an combinator for successor ($(+) \times 1^{(\wedge)}$, by the way). 
\begin{code}
cSuc :: E
cSuc = blog "x" (vx :+: c1)

chN :: Int -> E    -- allows inputting numerals in decimal.
chN n = let x = c0 : [ t :+: c1 | t <- x ] in x !! n

chN_suggestion = "test $ vz :^: vs :^: cN 7"
\end{code}

Luckily, we can print real church numerals in decimal,
and therefore print the first few values of a
function of type | Endo (Endo (Endo a)) |
\begin{code}
base10 :: Endo (Endo Int) -> Int
base10 n   = n succ 0

ffv_suggestion = "let eg n = (n * n) + n in map (base10 . eg) ff "
\end{code}
Note that all terms are divisible by 2.
(Division by two is a tricky matter...)

\newpage
\section{Displaying}

\subsection{Expressions} 
    
If one wants to investigate reduction sequences of arithmetical
expressions by running this code, one needs to display them.
To display expressions, we use the following code,
which is slightly less noisy than the built in show instance.
It should supress parentheses with associative operators, so
sometimes the same expression appears to be repeated.
(I think everything is right associative: as with |^|, so
with the other operators.)
I write the constant combinators in square brackets, which may
be considered noisy.
Actually, it might be more useful for printing to use one
level of superscripts, as when type-setting latex code.
There is at least half a chance of a human being making out
some structure in a string of arithmetical gibberish.

I don't understand precedences very well. I think the following
deals properly with associativity of |+| and |*|, and their
relative precedences (sums of products) but
also with the non-associativity of |^|. These nest to the right.
The best I can say is that by some miracle it seems to work as I expect.
\begin{code}
showE :: E -> Int -> String -> String
showE (V "^") _ = ("[^]"++)
showE (V "*") _ = ("[*]"++)
showE (V "+") _ = ("[+]"++)
showE (V ",") _ = ("[,]"++)
showE (V "~") _ = ("[~]"++)
showE (V "&") _ = ("[&]"++)
showE (C "^") _ = ("[^]"++)
showE (C "*") _ = ("[*]"++)
showE (C "+") _ = ("[+]"++)
showE (C ",") _ = ("[,]"++)
showE (C "~") _ = ("[~]"++)
showE (C "&") _ = ("[&]"++)
showE (V str) _ = (str++)
showE (a :+: b) p = opp p 0 (showE a 0 . (" + "++) . showE b 0)
showE (a :*: b) p = opp p 2 (showE a 2 . (" * "++) . showE b 2)
showE (a :^: b) p = opp p 4 (showE a 5 . (" ^ "++) . showE b 4)
-- because the below are wierd operators, I write them noisily.
showE (a :<>: b) p = opp p 4 (showE a 5 . (" <!> "++) . showE b 4)
showE (a :~: b) p = opp p 4 (showE a 5 . (" <~> "++) . showE b 4)
showE (a :&: b) p = opp p 4 (showE a 5 . (" <&> "++) . showE b 4)
parenthesize f = showString"(" . f . showString")"
opp p op = if p > op then parenthesize else id 
\end{code}

\begin{code}
instance Show E where showsPrec _ e = showE e 0 
\end{code}


\subsection{Trees and lists} 


Code to display a numbered list of showable things, throwing a line between entries.
\begin{code}
newtype NList a = NList [a]
instance Show a => Show (NList a) where
   showsPrec _ (NList es) = 
      (composelist . commafy ('\n':) . map showline . enum ) es
      where showline (n,e) = shows n . showString ": " . shows e 
\end{code}

\subsubsection{General list and stream amenities}
Code to pair each entry in a list/stream with its position.
\begin{code}
enum :: [a] -> [(Int,a)]
enum = zip [1..]
\end{code}

Code to compose a finite list of endofunctions.
\begin{code}
composelist :: [ a -> a ] -> a -> a
composelist = foldr (.) id
\end{code}

Code to insert a `comma' at intervening positions in a stream.
\begin{code}
commafy :: a -> [a] -> [a]
commafy c (x:(xs'@( _ : _ ))) = x:c:commafy c xs' 
commafy c xs = xs
\end{code}

Remove duplicates from a list/stream. The order in which entries are
first encountered is preserved in the output. 
\begin{code}
nodups :: Eq a => [a] -> [a] 
nodups [] = []
nodups (x:xs) = x : let xs' = nodups xs in
                    if   x `elem` xs'
                    then del1 x xs' id   --  filter (/= x) xs'
                    else xs'

-- delete exactly one occurrence of first argument in second
del1 c (c':cs) | c == c'  = (cs ^)    -- only invoked when c actually occurs
del1 c (c':cs)            = \ b -> del1 c cs (b . (c' :))
\end{code}

\subsection{Some top-level commands} 

The first reduction sequence. This is usually the most useful. One might type something like
\begin{spec}
         test $ vu :^: vz :^: vy :^: vx :^: cS
\end{spec}
\begin{code}
test :: E -> NList E
test  = NList . head . rss 
\end{code}

The normal form. This is occasionally useful when evaluation will obviously
terminate.  Only the normal form is displayed. 
\begin{spec}
         eval $ vz :^: vy :^: vx :^: cS
\end{spec}

Display the n'th reduction sequence in a reduction tree.
\begin{code}
nth_rs :: Int -> E -> NList E 
nth_rs n = NList . (!! n) . rss 
\end{code}

Display an entire |NTree a|.  Uses indentation in an attempt to make the
branching structure of the tree visible.
(Actually, this is almost entirely useless, except for very small expressions)
\begin{code}
newtype NTree a = NTree (Tree a)
instance Show a => Show (NTree a) where
   showsPrec p (NTree t) = 
     f id (1,t) where -- | f :: Show a => ShowS -> (Int,Tree a) -> ShowS  |
                      f pr (n,Node a ts) 
                           = (pr                      -- emit indentation
                             . showString "[" 
                             . shows n 
                             . showString "] "        -- child number
                             . shows a                -- node label
                             . showString "\n" 
                             . ( composelist 
                               . map (f (pr . showString "! "))
                               . enum ) ts)

\end{code}
We can try something like | let s = Ntree .reductTree in s (va :^: cS) |. 


Some basic stats on reduction sequence length. The number
of reduction sequences, and the extreme values of their lengths.
Be warned, this can take a very long time to finish on
even quite small examples. 
\begin{code}
stats_rss :: E -> (Int,(Int,Int))
stats_rss e = let (b0:bs) = map length (rss e)
              in (length (b0:bs), ( foldr min b0 bs , foldr max b0 bs) )
data DisplayStats = DisplayStats (Int,(Int,Int))
instance Show (DisplayStats) where
  showsPrec _ (DisplayStats (n,(l,h)))
              = ("There are "++) . shows n . (" reduction sequences"++)
                . (", varying in length between "++)
                . shows l . (" and "++) . shows h
\end{code}

\begin{code}
-- check that all reduction sequences terminate with the same expression
nf :: E -> [E]
nf = map last . rss 

-- might be useful
-- find the first suffix of a list that begins with a change
fd :: [E] -> Maybe [E]  -- first difference
fd [] = Nothing
fd [x] = Nothing
fd (x:xs@(y:_))   | x == y = fd xs
fd z@(x:xs@(y:_)) | x /= y = Just z
-- do not try this on a constant infinite stream.
\end{code}



\subsection{IO}

We might contemplate running these programs,
as opposed to just evaluating them. 
My suggestion is to think of the programs as
stream processors.

In this situation, the program can contain
at most one occurrence each of two special
variables, that are treated specially by the
execution system.  Linearity of these
occurrences is extremely important here.


The program runs in a state-space consisting
of an accumulator register (containing maybe
an expression), and an unconsumed stream of 
items from some stream type. For simplicity,
let us say the output also has the same type.
Two possibilities:
\begin{itemize}
\item tokens, as recognised by a scanner.
\item entire arithmetical expressions.
\end{itemize}

Each execution cycle of the program consumes
some initial segment (possibly null) of the input stream (stdin),
by finitely often reading items successively from it, and
atomically performs a corresponding action based on
the content of the accumulator.
(This might be to make it available on stdout.)

One can imagine two variables, or IO-combinators: |Rd| and |Wr|,
at which evaluation gets stuck (in hnf with those heads).
In the former case, an item is consumed, and passed as an
argument to the function that is the combinator's argument,
for further evaluation. 
In the latter case, the combinator's argument is appended to stdout.
(A table needed.)

The machine's state space is: |(control,stdin,stdout)|.
Its transitions are tabulated from left to right below.
\begin{center}
\newcommand{\vvec}[1]{\ensuremath{\left(\begin{array}{l} #1 \end{array}\right)}}
\begin{tabular}{ll}
  %\textit{hnf}   &
                   \textit{\underline{state}}  & \textit{\underline{state'}} \\[1ex]
  %| disp :^: Rd | &
                   $\vvec{ 
                        |disp :^: Rd| \\
                        |item :&: stdin| \\
                        |stdout| 
                   }$ 
                 & $\vvec{ 
                      |item :^: disp| \\
                      |stdin|  \\
                      |stdout| 
                  }$
  \\[2em]
  %| (item :&: nxt) :^: Wr | &
                  $\vvec{
                      | (item :&: nxt) :^: Wr | \\
                      | stdin  | \\
                      | stdout | 
                  }$
                & $\vvec{
                      |nxt| \\
                      |stdin| \\
                      |stdout :&: item| 
                  }$
\end{tabular}
\end{center}
The control state is really a cursor into an arithmetical expression.
I just show the subexpression in focus. 

The stream of output produced by the program is then
a potentially infinite history of items successively
written to stdout.

The history of input consumed by the program is then
a finite history of successively read stdin items.
(Or something similar ...)

\iffalse
\begin{code}
elim :: [a] -> (a,[a])
elim ts = (head ts, tail ts)
-- step_add' (a,f) = (a + f o, f . s)
-- step_mul' (a,f) = (a * f o, f . s)
step_add (a,f) = (a + head f, tail f)
step_mul (a,f) = (a * head f, tail f)
-- step f (a,w) = (f a (head w), tail w)
--   f a i  = a . (i:)
step (b,w) = (b . (head w:), tail w)            
postprocess b = b []
-- run :: X^w -> (E . E) (E (X^*),X^w) -> A^w 
run inp n = 
        post . iteration n --  (n step start)
        where
--              step :: (E (X^*), X^w) -> (E (X^*), X^w)
              step (b,w)  = ( tack b (head w:) , tail w )
--              start       :: (E (X^*), X^w)
              start       = (empty,inp)
--              empty :: E (X^*)
              empty       = id
--              tack  :: E (X^*) -> X -> E (X^*)
              tack b x    = b . x     -- tack = (.)
--              emit  :: E (X^*) -> X^*
              emit b      = b []      -- emit = ($[])
              post        = id        -- just for example
--              post  :: X^* -> A  -- some kind of fold
--              iteration :: (E . E) (E (X^*),X^w)  -> (E (X^*),X^w)
              iteration n = n step start
\end{code}
\fi

\newpage
\section{Parsing}

Is it even worth thinking about this?  The interpreter gives a
fine language for defining expressions, using let expressions, etc.

Something changed in ghc 7.10.2 making it a fuss to write simple parsers.
Applicative is bound up with monads, and they have stolen |<*>|. If
I hide that, I hide monads, and can't use do notation. 

\subsection{(parsing) combinators}

Choice: brain-dead parsing monad.
I don't understand the beaurocracy of instance declarations
well enough to use it properly.

Doesn't deal with input using pairing and flipping.
To be honest, I'm not sure how how precedences
and associativity should go with these operators.
(This means, with expressions like | a & b | and | a ~ b |.)

\begin{code}
-- import Control.Applicative

-- PARSERS.
-- t is the token type, v the parsed value. 
newtype Parser t v =  P {prun :: [t] -> [(v,[t])]}

instance Functor (Parser t) where
  fmap f (P pr) = P (\ ts -> [ (f v, ts') | (v,ts') <- pr ts])

instance Applicative (Parser t) where
  pure t = P (\ ts -> [(t,ts)])
  liftA2 = fby2' 

instance Monad (Parser t) where
  return   = eta
  a >>= b  = mmul (fmap b a) --  P (\ ts-> mmul (fmap b a))


\end{code}
\iffalse
{- 

instance Monad (Parser t) where
  return   = eta
  a >>= b  = Parser (\ ts-> mmul (fmap b a))

-}
\fi
\begin{code}
eta   :: v -> Parser t v   -- pure
eta v = P (\ ts -> [(v,ts)])

mmul :: Parser t (Parser t v) -> Parser t v
mmul pp = P (\ ts -> [(v,ts'') | (p,ts') <- prun pp ts, (v,ts'') <- prun p ts'] ) 

sat :: (t -> Bool) -> Parser t t
sat p  = P f where f (t:ts) | p t  =   [(t,ts)] 
                   f _             =   []

lit :: Eq t => t -> Parser t t
lit t  = sat (== t)

-- composes a sequence of N parsers that return things of the same type A
-- into a parser that returns a list in A* of length N. 
fby  :: Parser t a -> Parser t [a] -> Parser t [a] 
fby  =  liftA2 (:)   

fby2 :: Parser t a -> Parser t b -> (a -> b -> c) -> Parser t c
fby2 p q f
  = P (\s->  [ (f v v',s'')  |  (v,s') <- prun p s
                              , (v',s'') <- prun q s' ])

fby2' :: (a -> b -> c) -> Parser t a -> Parser t b -> Parser t c
fby2' f p q = fby2 p q f 


grdl :: Parser t a -> Parser t b -> Parser t b
grdr :: Parser t a -> Parser t b -> Parser t a

grdl' p q 
  = P (\s-> [ (b,s'') | (_,s') <- prun p s, (b,s'') <- prun q s' ])
grdl = fby2' (flip const) 

grdr' p q 
  = P (\s-> [ (a,s'') | (a,s') <- prun p s, (_,s'') <- prun q s' ])
grdr = fby2' const

paren' p   =  P (\s-> [ (a,s''')
                      | (_,s')   <- prun (lit Lpar) s
                      , (a,s'')  <- prun p s'
                      , (_,s''') <- prun (lit Rpar) s''])
paren p    =  grdl (lit Lpar) (grdr p (lit Rpar))


alt        :: Parser t a -> Parser t a -> Parser t a
alt p q    =  P (\s-> prun p s ++ prun q s)

alts       :: [Parser t a] -> Parser t a
alts ps    =  P (\s->concat [ prun p s | p <- ps ])

empty      :: Parser t [a]
empty      =  P (\s->[([],s)]) 

rep, rep1  :: Parser t a -> Parser t [a]
rep p      =  rep1 p `alt` empty 
rep1 p     =  p `fby` rep p 

repsep :: Parser t a -> Parser t b -> Parser t [a]
repsep p sep = p `fby` rep (sep `grdl` p)

\end{code}

\subsection{scanner}

A token is given by a string (possibly empty) of non-blank characters.
Two are the parentheses. Some of these are identifiers, that start with a
letter, and then proceed in some nice subset of the non-blank characters.
The rest, more or less, apart from the parentheses are deemed symbol tokens.

One of the token types is |Num|. This is an unused placeholder. 

\begin{code}
-- |tokens| turns a stream of characters into a stream of tokens.

is_alphabetic c  =  'a' <= (c :: Char) && c <= 'z' || 'A' <= c && c <= 'Z'
is_digit      c  =  '0' <= (c :: Char) && c <= '9' 
is_idch       c  =  c `elem` "_." || is_alphabetic c || is_digit c 
is_space      c  =  c == ' '
is_par        c  =  c `elem` "()"
is_symch      c  =  not (is_par c || is_space c)

data Tok   =  Id String  | Num Int |
              Sym String | Lpar | Rpar
              deriving (Show,Eq)

tokens     ::  String -> [Tok]
tokens []  =  []
tokens (c:cs) | isSpace c = tokens cs
tokens (inp@('(':cs)) 
           =  Lpar : tokens cs
tokens (inp@(')':cs)) 
           =  Rpar : tokens cs 
tokens ('[':cs)          -- hack to allow reading what I print
           =  id_t id cs where
                id_t b []                   =  [Sym (b [])]
                id_t b (']':cs)             =  Sym (b []): tokens cs 
                id_t b (c:cs)               =  id_t (b . (c :)) cs

tokens (c:cs) | is_alphabetic c
           =  id_t (c:) cs where
                id_t b []                   =  [Id (b [])]
                id_t b (c:cs) | is_idch c   =  id_t (b . (c :)) cs
                id_t b inp                  =  Id (b []): tokens inp 
tokens (c:cs) 
           =  id_t (c:) cs where
                id_t b []                   =  [Sym (b [])]
                id_t b (c:cs) | is_symch c  =  id_t (b . (c :)) cs
                id_t b inp                  =  Sym (b []): tokens inp 
\end{code}

\subsection{rudimentary grammar}
\begin{code}

variable, constant, atomic :: Parser Tok E

variable        =  P p where
                     p (Id st : ts)  = [(V st,ts)]
                     p _             = []
constant        =  P p where
                     p (Sym st : ts) = [(V st,ts)]
                     p _             = []
atomic          =  variable `alt` constant `alt` paren expression

additive, multiplicative, exponential, expression, discard :: Parser Tok E
additive        =  P       (  \s->
                           [  (fo (:+:) x xs ,s')
                           |  ((x:xs),s') <-
                                prun (repsep multiplicative (lit (Sym "+"))) s ])
multiplicative  =  P       (  \s->
                           [  (fo (:*:) x xs ,s')
                           |  ((x:xs),s') <-
                                prun (repsep exponential (lit (Sym "*"))) s ])
exponential     =  P       (  \s->
                           [  (fo (:^:) x xs ,s')
                           | ((x:xs),s') <-
                                prun (repsep atomic (lit (Sym "^"))) s ])
-- twiddles??
-- pairs??
expression      =  additive

discard         =  P      (\s-> [ (fo (:<>:) x xs ,s')
                               | ((x:xs),s') <-
                                    prun (repsep atomic
                                            ((lit (Sym "!"))
                                             `alt` lit (Sym "<>"))) s
                               ])

\end{code}

I'm unsure which of these `fold' operators to use.
I may have just broken the parser!
\begin{code}
fo  op s   []       =  s
fo  op s   (x:xs)  =   s `op` fo op x xs 
fo' op s   []       =  s    -- tail recursive
fo' op s   (x:xs)   =  fo' op (s `op` x) xs 
\end{code}

Useful to test parsing (which I haven't done recently).
\begin{code}
-- instance Read E where
--  readsPrec d = prun expression . tokens

rdexp :: String -> E
rdexp = fst . head . prun expression . tokens
\end{code}

\newpage
\section{Examples} 

This section codes some naturally occurring
combinators. 

\subsection{CBKIWSS'}

The combinators |C|, |B|, |K|, |I| and |W| can be encoded
as expressions in our calculus.
\begin{code}
cC, cB, cK, cI, cI', cW, c0 :: E
cC    = cM :*: cE :^: cM             -- M to one plus E to the E 
cB    = cE :*: cM :^: cM             -- M to the C
cK    = cE :*: c0 :^: cM             -- 0 to the C
-- | cI    = V"@" :^: V"0" |
cI'   = cE :*: cE :^: cM             -- E to the C
cW    = cE :*: (cE :+: cE) :^: cM    -- twice E to the cC
\end{code}

The `real-word' versions:
\begin{code}
combC        = (*) * (^) ^ (*)             --  |flip|, transpose. 
combB        = (^) * (*) ^ (*)             --  |(.)|, composition. |(*) ^ combC| 
combI        = naughtiness ^ (<>)          --  |id|. also |(^) * (^) ^ (*)|, inter alia
combK        = (^) * (<>) ^ (*)            --  |const|. |(<>) ^ combC|
combW        = (^) * ((^) + (^)) ^ (*)     --  diagonalisation. |((^) + (^)) ^ combC|
naughtiness  = error "Naughty!"
\end{code}

With |W|, there are several ways to define |S|.  One is by brute force: first define a linearised version |S'| with an extra argument: 
\begin{spec} 
    S' a b c1 c2 =    a c1 (b c2)
\end{spec}
Then define |S a b| (the normal S combinator) to be |W (S' a b)|.

It turns out that
\begin{spec}
    S'  =  (*) * ((*) *)
\end{spec}
which can also be written | (*) ^ (1 + (*)) |.
After a little calculation, we get something like:
\[
(\times) \times (\times)^{(\times)} \times (\times) \times
{((\wedge) \times {((\wedge) + (\wedge))}^{(\times)})}^{(\wedge)}
\]
% [*] * [*] ^ [*] * [*] * ([^] * ([^] + [^]) ^ [*]) ^ [^]
It cannot be controversial that this expression is less than entirely gorgeous.
B{\"o}hm's theory of logarithms gives a much nicer analysis of the |S| combinator (and it's
relatives).

Despite its brutality, the combinator |S'| is not without interest: 
\begin{spec}
  S     = S' * (*) * (W ^ (^))      -- $S' \times W^{C}$
  S'    = S' (*)
  C     = S' (^) 
  B     = S' (^) (*)           -- $(\times) ^ C$
  I     = S' (^) (^)           -- $(\wedge) ^ C$
  K     = S' (^) (<>)          -- $(\ZERO)  ^ C$
  W     = S' (^) ((^) + (^))   -- $((\wedge) + (\wedge)) ^ C$
  S' 1  = (*)  
\end{spec}

One can define the |S'| and |S| combinators as follows:
\begin{code}
combS' :: (a -> b -> c) -> (a1 -> b) -> a -> a1 -> c
combS :: (a -> b -> c) -> (a -> b) -> a -> c
combS' = let x = (*) in x * (x ^ x)
combS  = combS'  *  (*)  * (combW ^) 
\end{code}

The following expressions code the |S| and |S'| combinators
combinators.
\begin{code}
cS, cS'  :: E
cS       = cS' :*: cW :^: cB
cS'      = cM :*: (cM :^: cM)

-- the following is an example for checking that the logarithm apparatus is working.
-- It is a variant of the |S| combinator that should evaluate in the correct way. 
cSalt :: E 
cSalt    = blog "y" (blog "x" ( (vx :*: cPair) :+: (vy :*: cE )))
\end{code}
Try | test $ vy :^: vx :^: vb :^: va :^: cSalt |. It needs two extra variables.

\subsection{Sestoft's examples}

There is a systematic way of encoding data structures (pairs, tuples, whatnot) in the $\lambda$-calculus,
sometimes called Church-encoding.

Here are some examples in the list of predefined constants in 
Sestoft's Lambda calculus reduction workbench at 
http://raspi.itu.dk/cgi-bin/lamreduce?action=print+abbreviations
%http://www.dina.kvl.dk/~sestoft/lamreduce/index.html.

The first line shows the definition, the remaining lines show
the reduction to arithmetic form.

\begin{spec}
pair x y z = z x y 
           = y ^ x ^ z
           = (x ^ z) ^ (y^)
           = (z ^ (x ^)) ^ (y ^) 
pair x y   = (x^) * (y^) 
           = (y^) ^ ((x^)*)
pair x     = (^) * ((x^)*) 
           = ((x^)*) ^ ((^)*) 
           = ((x ^ (^))^(*)) ^ ((^)*)
pair       = (^)*(*)*((^)*)
\end{spec}
\begin{code}
cPair = cE :*: cM :*: (cE :^: cM)
\end{code}

Closely related to pairing is the Curry combinator,
which
satisfies | f^cCurry x y = f (x , y) |.
The following are alternate versions of this combinator.
\begin{code}
cCurry'   = cK :*: (cPair :^: cA)
cCurry    = cB :*: (cPair :^: cM)
cCurry_demo = (vz :^: (vy :^: vx :^: cPair) :^: vf) :&: (vz :^: vy :^: vx :^: vf :^: cCurry)
\end{code}
Try | test $ cK :^: cCurry_demo |, then | test $ c0 :^: cCurry_demo |.

\begin{spec}
tru x y  = x 
         = x^y^(<>)
         = (y^(<>))^(x^)
tru x    = (<>)*(x^) 
         = (x^)^((<>)*)
tru      = (^)*((<>)*)      
         = (<>)^C
\end{spec}

\begin{spec}
fal x y  = y 
         = y ^ x ^ (<>)
fal      = (<>)
\end{spec}

\begin{code}
cFalse = c0 
cTrue = c0 :^: cC    -- cK
cNot  = cC 
\end{code}

\begin{spec}
fst p    = p tru 
         = tru ^ p 
         = p^(tru^)
fst      = (tru^)
snd      = (fal^)
\end{spec}

\begin{code}
cFst = cTrue :^: cE 
cSnd = cFalse :^: cE 
\end{code}


\begin{spec}
iszero n = n (K fal) tru
         = n ((<>)*(fal^)) tru
         = tru ^ ((<>)*(fal^)) ^ n 
         = (n^(((<>)*(fal^))^))^(tru^)
iszero   = (((<>)*(fal^))^)*(tru^) 
\end{spec}
\begin{code}
cIszero  = cTrue :^: (cFalse :^: cK) :^: cPair
\end{code}



\subsection{Tupling, projections}

We use the usual notation $(a,b)$ for pairs.
In general

\begin{spec}
   (a1,...,ak) = (a1^) * ... * (ak^) 
\end{spec}

and the projection operators $\pi^k_i$ have the form 

\begin{spec}
   (K^i (K^j))^    where i + j + 1 = k 
\end{spec}

In fact the binary projections are defined using the booleans,
and other projections are defined using 
more general selector terms such as |\ x1 .. xn -> xi|.
This is done by applying | (^) | to the selector. 

\begin{spec}
    \ p -> p sel   = (sel^)
\end{spec}

The booleans are |K = (K^0) (K^1)| and |0 = (K^1) (K^0)|.  
Selecting the |i|'th element of a stack with |i+j+1| elements is |(K^i) (K^j)|. 

It may be interesting to remark that
\begin{spec}
    (a,a) = W pr a = (a^) * (a^) = a ^((^) + (^)) 
\end{spec}
So that |pr ^ W = (^) + (^) = W ^ C| 

TODO: code some expressions

\subsection{Permutations}

\begin{code}
perms_abc :: [E]
perms_abc =
  [ vc :^: vb :^: va    -- id
  , vc :^: va :^: vb    -- exp  (2-chain)
  , vb :^: vc :^: va    -- flip (2-chain)
  , va :^: vc :^: vb    -- bury/rotate-down (3-chain)
  , vb :^: va :^: vc    -- pair/rotate-up (3-chain)
  , va :^: vb :^: vc    -- flipped pair (2-chain)
  ]
inst_xyz :: E -> E
inst_xyz = (vz :^:) . (vy :^:) . (vx :^:)
bind_abc :: E -> E
bind_abc  =  blog "a" . blog "b" . blog "c"
c_perms :: [E] -- list of permutation combinators
c_perms   =  fmap (eval . bind_abc) perms_abc
see_perms = NList (fmap (eval . inst_xyz) c_perms) 
\end{code}

\subsection{Fixpoint operators}
Among endless variations, two fixed-point combinators stand out, Curry's and Turing's.
Both their fixed point combinators use self application.

This of course banishes us from the realm of combinators that Haskell can type,
but what the heck. There is syntax for it. We diagonalise exponentiation.
\begin{code}
cSap :: E
cSap = cE :^: cW
\end{code}
%
We call the self application combinator |sap|.
\begin{spec}
      sap x = x x = W (^) x = W 1 x 
  So  sap = (^)^W = 1^W
\end{spec}
%Note that the expressions |(^)^W| and |1^W| do not typecheck.

We call Curry's combinator simply $Y_C$.
\begin{spec}
    f^Y  = sap (sap * f)
      Y  = (sap *) * sap 
         = sap ^ ((*) + 1)
\end{spec}
$Y$ can thus be seen as applying
the successor of multiplication 
to the value |sap|.
\begin{code}
cY_C = cSap :^: cM :^: cSuc 
\end{code}

Turing's combinator is  |T ^ T| %, \ie{} |T ^ sap|
where $T x y = y (x x y)$.
\begin{spec}
     T x y      = y (x x y) = y (sap x y) = y ((sap^C) y x) 
     (T^C) y x  = y ((sap^C) y x) = (y . (sap^C) y) x 
     (T^C) y    = ((sap^C) y) * y 
     (T^C)      = (sap^C) + 1
     T          = ((sap^C) + 1)^C
                = sap ^ ( C * (+1) * C ) 
\end{spec}
$T$ can thus be seen as applying a kind of dual (with respect to the involution |C|) of the 
successor operator to the value |sap|.

Some expressions for 
Turing's semi-Y, and his Y.
\begin{code}
cT   = cSap :^: (cC :*: cSuc :*: cC)
cY_T = cT :^: cSap
\end{code}

Be careful when evaluating these things!

\subsection{Rotation combinators}

The following linear combinator |combR| `rotates' 3 arguments.
\begin{code}
combR    ::  a -> (b -> a -> c) -> b -> c
combR    =  (^) * (((*) * ((^)*))*)
combR'   =  (^) * (^) * ((*)*) 
\end{code}
Some such operation is often provided by the instruction
set of a `stack machine', to rotate the top three entries
on the stack. It can be seen as a natural extension of the
operation that flips (that is, rotates) the top two entries.

It can be encoded as follows:
\begin{code}
cR, cR_var     :: E
cR             = cC :^: cC 
cR_var         = (V "^") :*: (V "^") :*: (V "*") :^: (V "*")  -- a variant

-- an alias for left rotation. Could call it Load? (Load par3 to top)
-- abc to cab
cL          :: E
cL          = cPair
-- an alias for right rotation. Could call it Store? (Store top as par3)
-- abc to bca

cR_demo  = vc :^: vb :^: va :^: cR
cL_demo  = vc :^: vb :^: va :^: cL
\end{code}
It has a cousin, that rotates in the other direction.
This is actually the pairing combinator.

It so happens that the |cC| combinator and the |cR| are each
definable from the other. 

\begin{code}
cC'  =  cR :^: cR :^: cR 
cR'  =  cC :^: cC 
\end{code}

To be a little frivolous, this gives us a way of churning out
endless variants of the combinators |combR| and |flip|.

\begin{code}
flip', flip'' :: (a -> b -> c) -> b -> a -> c
flip' = flip flip (flip flip)  (flip flip) 
flip'' = flip' flip' (flip' flip')  (flip' flip') 
\end{code}

\subsection{Continuations} 

The function |^| which takes |a| to |a ^| pops up everywhere when playing
with arithmetical combinators.
It provides the basic means of interchanging the positions
of variables:
| a^b = b^(a^) = b^a^(^) |.

The continuation monad has a particularly simple expression in arithmetical
terms:
\begin{code}
cm_ret   = (^)                -- $\eta$
cm_join  = (^) ^ (*)          -- $\mu$
cm_map   = (*) * (*)
\end{code}

It doesn't matter what the `result type' is.  Letting it be |()|,
the functor can be defined as follows.
\begin{code}
type Cont a = (a -> ()) -> ()
\end{code}


\iffalse
The action on maps is
\begin{code}
cmap_CT :: E
cmap_CT = cM :*: cM
\end{code}
The unit |return| and multiplication |join| 
of this monad have simple arithmetical expressions. 
\begin{spec}
return      :: a -> CT a
join        :: CT (CT a) -> CT a
return a b  =  a ^ b            -- ie. |return = (^)|
f `join` s  =  f (return s)     -- ie. |join = ((^)*)|
\end{spec}
\fi
Here's their code.
\begin{code}
cRet, cMu, cMap  :: E
cRet = cE
cMu  = cE :^: cM
cMap  = blog "m" (blog "c" (blog "k"  (vm :*: vk) :^: vc))
\end{code}

We can simply define the bind operator from join and map.
\begin{code}
cBind :: E
cBind = let arg = vm :^: vc :^: cMap in blog "m" (blog "c" (arg :^: cMu))
\end{code}
Sadly, it's not very enchanting:
\[  (\wedge) \times (\wedge) \times (\wedge) \times (\times) ^ {(\times)} \times ((\times) \times (\wedge))^{(\times)}
\]
\iffalse
The bind operator |>>=| is not quite as simple.
\begin{spec}
 (m >>= f) s  = m (f^C . s)
 (m >>= f)    = (f^C) * m 
              = (^) * (f*) * m
 (>>=)^C f m  = (^) * (f*) * m
 (>>=)^C f    = ((^)*) . ((f*)*)
              = ((f*)*) * ((^)*)
 f^((>>=)^C)  = (f^(*))^(*) * (^)^(*)
 f^((>>=)^C)  = f^((*)*(*)) * (^)^(*)
\end{spec}

You may be interested in fancy control operators (like `abort'), and
flirtations with classical logic.
The following may reduce your cravings.

Peirce's law: | ((a->b) -> a) -> a |
is interesting because it is a formula of minimal logic.
It involves only the arrow, and not |0|.
\emph{Yet} you can prove excluded
middle |a or not a| from it, where `negation' is relativised to a generic
type $r$, as |not a = a -> r|.  So when defining something,
one has unrestricted access to these two cases.

Peirce's law postulates the existence of an algebra for
a certain monad, called `the Peirce monad' by Escardo\&co.

When `true' |0| (including efq) and hence true negation is
added, to minimal logic, Peirce's law implies not just
excluded middle, but full classical logic with involutive
negation, \ie{} $\neg(\neg a) = a$. 

To suppose the negation of Peirce's law leads
to an absurdity. (We don't need efq for this.)
\begin{spec}
      not Peirce   =   not a  &  ((a->b)->a)
                   =>  not a  &  not (a->b)
                   =   not a  &  not b & a 
\end{spec}
We cannot hope to prove Peirce's law, but we might expect to
prove it's transform by the continuation monad |((a -> CT b) -> CT a) -> CT a|,
in which all the arrows |a -> b| have been turned into Kleisli arrows
|a -> CT b|.  Or maybe even |((a -> b) -> CT a) -> CT a|.
We can ask what such a thing would look like expressed with arithmetical
combinators. 
I once made an effort to do this, and got the following result (though it
is pretty certain there are some errors here):
\iffalse
\begin{spec}
(((*) * ((^) * 0 ^ (*)) ^ (^)) ^ (*) * (^)) * ((^) + (^)) ^ (*)
\end{spec}
\fi
$$
(((\times) \times ((\wedge) \times 0^{(\times)})^{(\wedge)})^{(\times) \times (\wedge)}) \times ((\wedge) + (\wedge))^{(\times)}
$$ 
Well, if that's an arithmetical expression of classical logic, it's neither very enlightening or beguiling!
One can however see some additive features here, namely $(\wedge) + (\wedge)$ and $0$. I find that
reassuring. 

One can ask the same questions with respect to the Peirce monad.


The monadic apparatus can be encoded as follows
\begin{code}
ct         ::  E -> E
ct a       =   a :^: cE                     -- unit
cb         ::  E -> E -> E
cb m f     =   cE :*: (f :^: cE) :*: m  -- bind

cCTret, cCTjoin, cCTbind ::  E
cCTret     =   cE
cCTjoin    =   cCTret :^: cM
cCTbind    =   blog "m" (blog "f" (cb (V"m") (V"f")))
\end{code}
It may be interesting to point out that
$(a,b) = a^{[\wedge]} \times b^{[\wedge]} = \eta a \times \eta b$
where $\eta$ is the unit of CT.

\fi

\subsection{Peano numerals}

Oleg Kiselyov
%\cite{oleg} 
was once and may still be interested in what I think he calls or once called `p-numerals'.These 
are (so to speak) related to primitive recursion as the Church
numerals are related to iteration.  So the successor of n is 
not 
\begin{spec}
  \ f,z->f(n f z)  
\end{spec}
as it is with Church numerals, but rather
\begin{spec}
 \ f,z->f n (n f z) 
\end{spec}
I have heard other people than Oleg express an interest in this encoding. It's not un-natural. 

So, letting the variable |n| vary over p-numerals, one has
\begin{spec}
   n b a  = b (n-1) (b (n-2) ... (b 1 (b (<>) a)) ...)   
\end{spec}

Using the combinators of this paper, one can derive
\begin{spec}
   n b    = b (<>) * b 1 * ... * b (n-2) * b (n-1) 
          = b^((<>)^) * b^(1^) * ... * b^((n-2)^) * b^((n-1)^) 
          = b^(((<>)^) + (1^) + ... + ((n-2)^) + ((n-1)^)) 
\end{spec}

By exponentiality ($\zeta$), 
\begin{spec}
   n      = ((<>)^) + (1^) + ... + ((n-2)^) + ((n-1)^) 
\end{spec}

%(Remember that all the numbers here are to be understood as p-numerals!) 

In fact, if |Osucc| is Oleg's successor, we have | Osucc n = n + (n^) |. 
\begin{spec}
  (<>)_p  = (<>)
  1_p  = ((<>)^) 
  2_p  = ((<>)^) + (((<>)^)^) 
  3_p  = ((<>)^) + (((<>)^)^) + ((((<>)^) + (((<>)^)^))^)
  ...
\end{spec}


One may be reminded here of von-Neumann's representation for ordinals, which has $n \mapsto n \cup \{n\}$.for its successor operation,
and the empty set $\{\}$ for its origin.
\[
\newcommand{\MT}{\{\}}
\newcommand{\B}[1]{\{#1\}}
\begin{array}{rcl}
  0  &=& \MT            \\
  1  &=& \B{\MT}\\
  2  &=& \B{\MT,\B{\MT}}\\
  3  &=& \B{\MT,\B{\MT},\B{\MT,\B{\MT}}}\\
  && ...
\end{array}
\]
Clearly the operation of raising to the power of exponentiation (that
takes |n| to |(n^)|) plays the role of the singleton operation  $n \mapsto \{n\}$.

\begin{code}
cOsuc :: E -> E
cOsuc e = e :+: (e :^: cE)

cOzero :: E
cOzero = V"0"

cO :: Int -> E    -- allows inputting numerals in decimal.
cO n = let x = cOzero : [cOsuc t | t <- x ] in x !! n 
\end{code}
\subsection{sgbar, \etc{}}


|sgbar|, or exponentiation to base zero, is the function which is 1 at
0, and only at 0.  On numbers, it is the characteristic
function of those that are zero. 
\begin{code}
sgbar  :: C b2 (a -> Endo b1)      -- eg C x x where x = N b.
sgbar  = ((<>) ^)                  -- real-world

cSgbar :: E
cSgbar = c0 :^: cE                -- code

sgbar' :: Endo (N a)
sgbar' n s z = n (const z) (s z)

cSgbar' :: E
cSgbar' = let v1 = vz :^: vs
              ef = vz :^: cK
          in (blog "n" (blog "s" (blog "z" (v1 :^: ef :^: vn ))))
\end{code}

Using |sgbar|, we can define |sg|, which is 0
at 0, and 1 elsewhere (the sign function, or the characteristic
function of the non-zero numbers).
\begin{code}
sg :: ((a1 -> Endo b2) -> (a2 -> Endo b3) -> c) -> c
sg = sgbar * sgbar

sg' :: Endo (N a)
sg' n s z   = n (const (s z)) z 

cSg  = cSgbar :*: cSgbar
cSg' = let v1 = vz :^: vs
           ef = v1 :^: cK
       in (blog "n" (blog "s" (blog "z" (vz :^: ef :^: vn ))))
\end{code}
It may be clearer to write it |sg a = (<>) ^ (<>) ^ a|.  Think of double negation. 

Using |sg| and |sgbar|, we can implement a form of boolean
conditionals.  | IF b=0 THEN a ELSE c | 
can be defined as | a*sg(b)+c*sgbar(b) |.  

In fact we have forms of definition by finite cases.


%\iffalse

\section{Benedicto benedicatur} 

Examples I once used, with |test|, to demo some reduction sequences.
Little thought has been given to this.

\begin{code}

demo1Add    = let  d  =  va :+: vb      in vx :^: d
demo1Zero   = let  d  =  V"0"           in vx :^: d 
demo1Mul    = let  d  =  va :*: vb      in vx :^: d
demo1One    = let  d  =  V"1"           in vx :^: d

-- show that the logarithm of an exponential behaves as expected
demoExp     = let  d = (va :^: cPair) :*: (vb :^: cE)
              in   vx :^: d
demoExp'    = let  d = (va :*: cPair) :+: (vb :*: cE)
              in   vy :^: vx :^: d

-- two equivalent codings                 
demoAdd     = let  c = (va :^: cE) :+: (vb :^: cE)  
                   d = cPair :*: cM :*: c :^: cE      -- curry c
              in   vz :^: vy :^: vx :^: d
demoAdd'    = let  c = (va :^: cE) :+: (vb :^: cE)
                   d = cPair :+: c :^: cK             -- curry c
              in   vz :^: vy :^: vx :^: d

demoNaught  = let  d = c0 :*: c0 :^: cE in d
\end{code}

One can think of addition as repetition of the successor operation,
as mutiplication as repetition of addition to zero,
and of exponentiation as repetition of mutiplication to one.
The successor operation can be defined as |(1 +)| or |(+ 1)|.

\begin{code}
demoSuc      = c1 :^: cA
demoSuc'     = c1 :^: cA :^: cC

demoPlus     = demoSuc :^: cPair
demoTimes    = demoPlus :*: (c0 :^: cPair :^: cC)
demoPower    = demoTimes :*: (c1 :^: cPair :^: cC)

demoPlus'     = demoSuc' :^: cPair
demoTimes'    = demoPlus' :*: (c0 :^: cPair :^: cC)
demoPower'    = demoTimes' :*: (c1 :^: cPair :^: cC)
\end{code}

You can for example ask ghci to evaluate | test $ demoAdd' |.
%\fi
\end{document}

Safe place for debris:
Don't  use code environment!

*Main> let l = V"*" :*: cB :*: (V"+" :^: V"*") ; r = V"*" :+: (V"+" :^: cK) :+: (V"*" :*: V"*") in test (vc :^: vb :^: va :^: l)

  let sb = (vc :^: vb) :^: vc :^: va ; s = blog "a" (blog "b" (blog "c" sb)) ; k = blog "a" (blog "b" va) in test $ vw :^: vz :^: vy :^: vx :^: s

let b = vz :^: vy :^: vx ;
    p0   = blog "z" . blog "y" . blog "x" ;    -- converse pair = cPair :^: cC       swap(a,c)
    p1   = blog "z" . blog "x" . blog "y" ;    -- rotation      = cR    = cC :^: cC
    p2   = blog "y" . blog "x" . blog "z" ;    -- exponential   = cE                 swap(a,b)
    p3   = blog "y" . blog "z" . blog "x" ;    -- pair          = cPair = cE :*: cC 
    p4   = blog "x" . blog "y" . blog "z" ;    -- identity      = c1    = cC :*: cC 
    p5   = blog "x" . blog "z" . blog "y" ;    -- flip          = cC                 swap(b,c)
    p = (p0 b :&: p1 b :&: p2 b :&: p3 b :&: p4 b :&: p5 b) in test $p

let t = cE :*: cC ; vec h = vc :^: vb :^: va :^: h in test $ vx :^: (vec t :&: vec cPair)



\iffalse
 test $ vx :^: ((va :^: cPair) :*: (vb :^: cE))
--demonstrates that a ^ b = a ^ cPair :*: b ^ cE

-- demonstrates log-like behaviour of _^K.
test $ inst_xyz $ (va :^: (cK :*: cE) :+: vb :^: (cK :*: cE)) :^: cCurry -- (va :+: vb) :^: cK

-- demonstrates (+ b) as iteration of (+1).
let suc = c1 :^: cA :^: cC ; plus b = (suc :^: cPair) :*: (b :^: cE) in test $ vy :^: vx :^: plus c3

-- a definition of addition as iterated successor
let  suc = c1 :^: cA :^: cC ; t = (cE :*: (suc :^: cPair) :^: cM) :^: cC in test $ c3 :^: c0 :^: t

-- t is a redefinition of the addition combinator
let  suc = c1 :^: cA :^: cC ; t = (cE :*: (suc :^: cPair) :^: cM) :^: cC in test $  vy :^: vx :^: (cA :*: (c1 :^: cE))  -- [+]*(1^) 



let m = (cSuc :^: cE) :*: (c0 :^: cPair :^: cC) ; e = (m :^: cC) :*: (c1 :^: cPair :^: cC) in test $ vz :^: vs :^: c3 :^: c2 :^: e

let a = cSuc :^: cE ; m = (cSuc :^: cE) :*: (c0 :^: cPair :^: cC) ; e = (m :^: cC) :*: (c1 :^: cPair :^: cC) in test $ vs :^: c3 :^: c2 :^: e

\fi
