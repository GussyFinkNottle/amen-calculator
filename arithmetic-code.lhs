\documentclass{article}
\usepackage{hyperref}
%include polycode.fmt
%lhs2TeX.fmt
%format :^: = ":\!\wedge\hspace{-0.5ex}:\mbox{}" 
%format :*: = ":\!\times\hspace{-0.5ex}:\mbox{}" 
%format :+: = ":\!+\hspace{-0.5ex}:\mbox{}" 
%format ^ = "\wedge"
%format * = "\times"
%format <> = "\!\mathop{{}^{{}^{\cdot}}}\!"


\title{The AMEN calculator}
\newcommand{\ie}{\textit{ie.\hspace{0.5ex}}}
\newcommand{\eg}{\textit{eg.\hspace{0.5ex}}}
\newcommand{\etc}{\textit{\&{}co.\hspace{0.5ex}}}
\newcommand{\logarythm}{$\lambda$ogarythm}

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
               ((*),(^),(+),(<>)
               ,(<*>),(<^>),(<+>),(<<>>)
               ,(:^:),(:*:),(:+:),(:<>:)
               ,pi
               )
infixr 8  ^   
infixr 7  *   
infixr 6  +   
infixr 9  <>  

main :: IO ()        -- Do something with this later.
main =  let eg = " test $ vc :^: vb :^: va :^: cC "
        in putStrLn
             ("Load in ghci and type something like: " ++ eg)
\end{code}

\section{Real-world arithmetical combinators}

Here are some simple definitions of binary operations corresponding to the 
arithmetical combinators: 
\begin{code}
a ^ b  = b a
a * b  = \c -> (c ^ a) ^ b
a + b  = \c -> (c ^ a) * (c ^ b)
a `naught` b = b
\end{code}

Instead of |naught|, one can use the infix operator |(<>)|, that looks
a little like a `|0|'. It discards its left argument, and returns its right. 
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

The type-schemes inferred for the definitions are as follows:
\begin{code}
(^)      :: a -> (a -> b) -> b
(*)      :: (a -> b) -> (b -> c) -> a -> c
(+)      :: (a -> b -> c) -> (a -> c -> d) -> a -> b -> d
(<>)     :: a -> b -> b
one      :: a -> a
\end{code}
Anyone should think:
\begin{itemize}
\item continuation transform
\item action of contravariant functor |_ -> c| on morphisms
\item lifted version of the above
\item |const id|
\item |id|
\end{itemize}

\subsection{Infinitary operations: streams and lists}
For infinitary operations (this may come later) I need these
\begin{code}
pfs :: (a -> a -> a) -> a -> [a] -> [[a]]
pfs op ze xs = [ b ze | (b,_) <- pfs' xs id]
               where pfs' (x:xs) b = pfs' xs (b . (op x))

type EE x = x -> x
pi    :: [EE a] -> [[EE a]]
sigma :: [a -> EE b] -> [[a -> EE b]]
pi    = pfs (*) one
sigma = pfs (+) zero

type N x = EE (EE x)
index        :: N [a] -> [a] -> a
index n         = head . n tail
-- note index 0 is head

type C x y = (x -> y) -> y
ret :: x -> C x y
ret = (^)
mu  :: C (C x y) y -> C x y
mu mm k = mm (ret k)
{- The types |x -> C x x| and |N x| are isomorphic. -}
{- The same combinator is used in both inverse directions! -}
myflip :: (x -> C x x) -> N x
myflip = flip 
myflip' :: N x -> x -> C x x
myflip' = flip 

-- any of the following type statements will do
mydrop :: C (EE [a]) y 
-- | mydrop :: (([a] -> [a]) -> t) -> t  |
-- | mydrop :: (EE [a] -> t) -> t  |
-- | mydrop :: N [a] -> EE [a]  |
mydrop n  = n tail
mydrop'   = ($ tail)
\end{code}
|pfs| is applied only to streams, and returns a stream.
Think of it is a stream of finite lists, namely the list of finite
prefixes of a stream. Then we fold an operation over each list, starting
with a constant. 

\subsection{Booleans}

I wanted to look at Church encoding of booleans.
The following can all be restricted in such a way
that |a|, |b| and |c| are the same.  This is analogous to
the situation with Churc numerals.
\begin{code}
type I2 a b c = a -> b -> c
impB  ::  I2 (I2 a b c) (I2 b d a) (I2 b d c)
orB   ::  I2 (I2 a b c) (I2 a d b) (I2 a d c)
andB  ::  I2 (I2 a b c) (I2 d b a) (I2 d b c)
posB  ::  I2 a b a
nilB  ::  I2 a b b
impB  a b p n  =  a (b p n) p
orB   a b p n  =  a p (b p n)  -- the same as numerical addition
andB  a b p n  =  a (b p n) n
posB  =  const 
nilB  =  zero
if0   :: I2 a b c -> I2 b a c 
ifP   :: a        -> a
ifP   =  id 
if0   =  flip
\end{code}

\section{Syntax for arithmetical expressions}

The defining equations above generate an equivalence relation between
(possibly open) terms in a signature with eight operators:

\begin{itemize}
\item 4 constants |(^)|, |(*)|, |(+)| and |(<>)|
\item 4 binary operators |_^_|, |_*_|, |_+_| and |_<>_|
\end{itemize}

This is the least equivalence relation
extending the definitions, congruent to all operators in the signature.  
This means that equations between open terms can be proved by
substituting equals for equals.

One can also allow instances of the following ``$\zeta$-rule'' in proving equations.
\begin{center}
    \begin{tabular}{c} |x ^ a = x ^ b|  $\mbox{}\Longrightarrow\mbox{}$ |a = b| \end{tabular}
\end{center}
with the side condition that |x| is fresh to both |a| and |b|.

The $\zeta$-rule is a cancellation law. It expresses
`exponentiality':
two expressions that behave the same as exponents of a generic base
(as it were, a cardboard-cutout of a base) are equivalent. 
I shall call this equivalence relation $\zeta$-equality.  Any equation I assert
should be interpreted as $\zeta$-equations, unless I say otherwise.

It may be that to determine the behaviour of an expression as an
exponent, we have to supply it with more than one base-variable.
Sometimes, `extra' variables play a role in allowing computations
to proceed, and subsequently can be cancelled.
  
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


It is convenient to have atomic constants identified by arbitrary strings.
The constants |"+"|, |"*"|, |"^"|, |"0"|, |"1"| are treated specially.
\begin{code}
(cA, cM, cE, c0, c1, cC_new, cPair_new, c0')
  = ( V"+"        -- AMEN
    , V"*"
    , V"^"
    , V"0"
    , V"1"        -- de trop combinators
    , V"~"        -- flip
    , V"&"        -- pairing
    , V"<>"       -- discard left-hand argument
    )
\end{code}

For each arithmetical operator, we define a function that takes two
arguments, and (sometimes) returns a `normal' form of the expression 
formed with that operator.  (This doesn't allow us to trace reduction
sequences -- we turn to that later.) The definitions correspond to the
transitions of an arithmetical machine. 

I have no idea whether the following are rational. Just my current hunch.
\begin{code}
infixr 9  <<>>
infixr 8  <^> 
infixr 7  <*>
infixr 6  <+>
\end{code}
\begin{spec}
infixr 5  <&>
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
          V"0"           ->  b :^: b
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

The machinery is controlled by a single (case-)table of top-level
reductions, in the function |tlr| below.
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
             (a :+: (b :+: c))    ->  [ (a :+: b) :+: c          ]  --  space reuse
             (V "0" :+: a)        ->  [ a                        ]  --  drop1
             (a :+: V "0")        ->  [ a                        ]  --  drop1
             (a :*: (b :+: c))    ->  [ (a :*: b) :+: (a :*: c)  ]  --  2 to 3
             (a :*: V "0")        ->  [ c0                       ]  --  drop1
             (a :*: (b :*: c))    ->  [ (a :*: b) :*: c          ]  --  reuse
             (V "1" :*: a)        ->  [ a                        ]  --  drop1
             (a :*: V "1")        ->  [ a                        ]  --  drop1
             (a :^: (b :+: c))    ->  [ (a :^: b) :*: (a :^: c)  ]  --  2 to 3
             (a :^: V "0")        ->  [ c1                       ]  --  drop1
             (a :^: (b :*: c))    ->  [ (a :^: b) :^: c          ]  --  reuse
             (a :^: V "1")        ->  [ a                        ]  --  drop1   -- idle
             (a :^: b :^: V "+")  ->  [ b :+: a                  ]  --  drop1
             (a :^: b :^: V "*")  ->  [ b :*: a                  ]  --  drop1
             (a :^: b :^: V "^")  ->  [ b :^: a                  ]  --  drop1   -- top 2 swap
             (a :^: b :^: V "0")  ->  [ b :<>: a                 ]  --  drop1   -- indirection
             (a :^: b :^: V "~")  ->  [ b :~: a                  ]  -- 
             (a :^: b :^: V "&")  ->  [ b :&: a                  ]  -- 
             (a :^: (b :&: c))    ->  [ c :^: b :^: a            ]  -- a 2-chain 
             (a :^: (b :~: c))    ->  [ b :^: a :^: c            ]  -- a 3 chain 
             (_ :<>: b)           ->  [ b                        ]  --  drop1
             (V "0" :^: V "+")    ->  [ c1                       ]  -- +/* left units 0/1
             (V "1" :^: V "*")    ->  [ c1                       ]
             (V "~" :*: V "~")    ->  [ c1                       ]  -- missing a square root, I think
             (V "^" :*: V "~")    ->  [ V "&"                    ]  -- apparently. Other interdependencies?
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

The function |sites| returns (in top down preorder: root, left, right \ldots) 
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
                       (a :<>: b)  ->  sites b          -- DANGER! indirection
                       _           ->  []               -- no internal sites
            where
              h op a b   =  i ++ ii
                            where
                              i   =  [ ((a `op`) . f,p) | (f,p) <- sites b ]  -- right operand b first
                              ii  =  [ ((`op` b) . f,p) | (f,p) <- sites a ]
\end{code}
It should be noted that `far-right' sites come first. This is just a mirror image of the
normal situation, where the far-left argument comes first.

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
usually to be the one that interest me. 



\section{B{\"o}hm's \logarythm} 

This code generating the \logarythm{} of an expression
with respect to a variable name.

B{\"o}hm's combinators
\begin{code}
cBohmA a b = let g = a :^: V"^" :+: b :^: V"^" in 
             let curry  g = cPair :+: g :^: cK in   -- Bohm's original
             let curry' g = cPair :*: cM :*: (g :^: cE)  -- another without additive apparatus 
             in curry' (a :^: V"^" :+: b :^: V"^")
cBohmE a b = a :*: cPair :+: b :*: V"^"
cBohmM a b = a :+: b              
cBohm0 a   = c0 :*: (a :^: cE)
\end{code}
These have the crucial properties
\begin{spec}
   x ^ cBohmA a b  = (x ^ a) + (x ^ b)
   x ^ cBohmM a b  = (x ^ a) * (x ^ b)
   x ^ cBohmE a b  = (x ^ a) ^ x ^ b
   x ^ cBohm0 a    = a
\end{spec}
used in defining the logarithm.

This code can perhaps be slightly refined to keep the size
of its logarithms down. The cases to look at are those where
the variable occurs in just one of a pair of operands.
\begin{code}
blog v e | not (v `elem` fvs e) = cBohm0 e 
blog v e = case e of 
          a :+: b -> {- cBohmA (blog v a) (blog v b) -}
                     case (v `elem` fvs a,v `elem` fvs b) of
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
                        _            -> cBohmE (blog v a) (blog v b)

          V nm     -> if nm == v then c1 else cBohm0 e
\end{code}

The following function returns a list of all the variable names occurring in an expression.
The list is returned in the order in which variables first occur in a depth-first scan.
\begin{code}
fvs e = nodups $ f e []
               where f (V nm) = if nm `elem` ["0", "1", "^", "*", "+", "@", ",", "~", "."]
                                then id else (nm:)
                     f (a :^: b)   = f a . f b 
                     f (a :*: b)   = f a . f b 
                     f (a :+: b)   = f a . f b
                     f (a :<>: b)  = f b
\end{code}



\appendix

\section{Bureaucracy and gadgetry}

To save typing, names for all single-letter variables
\begin{code}
( va, vb, vc, vd,
  ve, vf, vg, vh,
  vi, vj, vk, vl,
  vm, vn, vo, vp,
  vq, vr, vs, vt,
  vu, vv, vw, vx, vy, vz) 
  = ( V"a", V"b", V"c", V"d",
      V"e", V"f", V"g", V"h",
      V"i", V"j", V"k", V"l",
      V"m", V"n", V"o", V"p",
      V"q", V"r", V"s", V"t",
      V"u", V"v", V"w", V"x", V"y", V"z")
\end{code}

We code a few useful numbers as expressions.
\begin{code}
c2, c3, c4 , c5, c6, c7, c8, c9, c10 :: E
c2       = c1      :+: c1
c3       = c2      :+: c1 
c4       = c2      :^: c2
c5       = c3      :+: c2
c6       = c3      :*: c2
c7       = c3      :+: c4
c8       = c2      :^: c3
c9       = c3      :^: c2
c10      = c2      :*: c5
\end{code}
|c0| and |c1| have already been defined.

It is time we had an combinator for successor ($(+) \times 1^{(\wedge)}$, by the way). 
\begin{code}
cSuc :: E
cSuc = blog "x" (vx :+: c1)

cN :: Int -> E    -- allows inputting numerals in decimal.
cN n = let x = c0 : [ t :+: c1 | t <- x ] in x !! n

cN_suggestion = "test $ vz :^: vs :^: cN 7"

{- Somehow allow decimal output, when possible? -}
{- |dN :: N a -> Int   |-}
{- |dN e = e (+1) 0 |-}

\end{code}


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
-- because the below are wierd operator, I make them noisy.
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

\subsubsection{General list and stream stuff}
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
nodups (x:xs) = x : nodups (filter (/= x) xs)
\end{code}

\subsection{Some top-level commands} 

The first reduction sequence. This is by far the most useful. One might type something like
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

The machine's state space is: |(stdin,stdout,control)|.
\begin{center}
\newcommand{\vvec}[1]{\ensuremath{\left(\begin{array}{l} #1 \end{array}\right)}}
\begin{tabular}{ll}
  %\textit{hnf}   &
                   \textit{\underline{state}}  & \textit{\underline{state'}} \\[1ex]
  %| disp :^: Rd | &
                   $\vvec{ 
                        |stdout| \\
                        |e :&: stdin| \\
                        |disp :^: Rd| }$ 
                                      & $\vvec{ 
                                           |stdout| \\
                                           |stdin|  \\
                                           |e :^: disp| }$ \\[2em]
  %| (item :&: nxt) :^: Wr | &
                   $\vvec{  | stdout | \\
                            | stdin  | \\
                            | (item :&: nxt) :^: Wr |
                         }$
                                      & $\vvec{ |stdout :&: item| \\
                                                |stdin| \\
                                                |nxt|}$
\end{tabular}
\end{center}

The stream of output produced by the program is then
a potentially infinite history of successive accumulator contents.



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

\section{Parsing}

Is it even worth thinking about this?  The interpreter gives a
fine language for defining expressions, using let expressions, etc.

Something changed in ghc 7.10.2 making it a fuss to write simple parsers.
Applicative is bound up with monads, and they have stolen |<*>|. If
I hide that, I hide monads, and can't use do notation. 

\subsection{(parsing) combinators}
\begin{code}

-- PARSERS.
-- t is the token type, v the parsed value. 
newtype Parser t v =  Parser {prun :: [t] -> [(v,[t])]}


sat :: (t -> Bool) -> Parser t t
sat p  = Parser f where f (t:ts)  =   if p t then [(t,ts)] else []
                        f []      =   []

lit :: Eq t => t -> Parser t t
lit t  = sat (== t)

-- composes a sequence of N parsers that return things of the same type A
-- into a parser that returns a list in A* of length N. 
fby :: Parser t a -> Parser t [a] -> Parser t [a] 
fby p q 
  = Parser (\s-> [((v:vs),s'') | (v,s') <- prun p s, (vs,s'') <- prun q s' ])

fby2 :: Parser t a -> Parser t b -> (a -> b -> c) -> Parser t c
fby2 p q f
  = Parser (\s->
              [ (f v v',s'')  | (v,s') <- prun p s
                              , (v',s'') <- prun q s' ])

grdl :: Parser t a -> Parser t b -> Parser t b
grdr :: Parser t a -> Parser t b -> Parser t a
grdl p q 
  = Parser (\s-> [ (b,s'') | (_,s') <- prun p s, (b,s'') <- prun q s' ])
grdr p q 
  = Parser (\s-> [ (a,s'') | (a,s') <- prun p s, (_,s'') <- prun q s' ])
paren p 
  = Parser (\s-> [ (a,s''') | (_,s')   <- prun (lit Lpar) s
                            , (a,s'')  <- prun p s'
                            , (_,s''') <- prun (lit Rpar) s''])


alt :: Parser t a -> Parser t a -> Parser t a
alt p q  = Parser (\s-> prun p s ++ prun q s)

alts :: [Parser t a] -> Parser t a
alts ps  = Parser (\s->concat [ prun p s | p <- ps ])

empty :: Parser t [a]
empty = Parser (\s->[([],s)]) 

rep, rep1 :: Parser t a -> Parser t [a]
rep p = rep1 p `alt` empty 
rep1 p = p `fby` rep p 

repsep :: Parser t a -> Parser t b -> Parser t [a]
repsep p sep = p `fby` rep (sep `grdl` p)

\end{code}

\subsection{scanner}
\begin{code}
-- SCANNER.
-- turns a stream of characters into a stream of tokens.

-- import Data.Char

is_alphabetic c = 'a' <= (c :: Char) && c <= 'z' || 'A' <= c && c <= 'Z'
is_digit      c = '0' <= (c :: Char) && c <= '9' 
is_idch     c = c `elem` "_." || is_alphabetic c || is_digit c 
is_space      c = c == ' '
is_par        c = c `elem` "()"
is_symch      c = not (is_par c || is_space c)

data Tok   =  Id String | Num Int |
              Sym String | Lpar | Rpar
              deriving (Show,Eq)
tokens     ::  String -> [Tok]
tokens []  =  []
tokens (c:cs) | isSpace c = tokens cs
tokens (inp@('(':cs)) 
           =  Lpar : tokens cs
tokens (inp@(')':cs)) 
           =  Rpar : tokens cs 
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

\subsection{grammar}
\begin{code}
-- GRAMMAR
variable, constant, atomic :: Parser Tok E

variable        =  Parser p where
                       p (Id st : ts) = [(V st,ts)]
                       p _            = []
constant        =  Parser p where
                     p (Sym st : ts) = [(V st,ts)]
                     p _            = []
atomic          =  variable `alt` constant `alt` paren expression

additive, multiplicative, exponential, expression, discard :: Parser Tok E
additive        =  Parser (\s-> [ (fo (:+:) x xs ,s')
                                | ((x:xs),s') <-
                                    prun (repsep multiplicative (lit (Sym "+"))) s ])
multiplicative  =  Parser (\s-> [ (fo (:*:) x xs ,s')
                                | ((x:xs),s') <-
                                     prun (repsep exponential (lit (Sym "*"))) s ])
exponential     =  Parser (\s-> [ (fo (:^:) x xs ,s')
                                | ((x:xs),s') <-
                                     prun (repsep atomic (lit (Sym "^"))) s ])
expression      =  additive

discard         =  Parser (\s-> [ (fo (:<>:) x xs ,s')
                               | ((x:xs),s') <-
                                    prun (repsep atomic
                                            ((lit (Sym "!"))
                                             `alt` lit (Sym "<>"))) s
                               ])

\end{code}

\begin{code}
-- foldr1 ? 
fo op fst [] = fst
fo op fst (x:xs) = fst `op` fo op x xs 

-- instance Read E where
--  readsPrec d = prun expression . tokens

rdexp :: String -> E
rdexp = fst . head . prun expression . tokens
\end{code}


\section{Examples} 

In this section, we encode some naturally occurring
combinators as expressions.

\subsection{CBKIWSS'}

The combinators |C|, |B|, |K|, |I| and |W| can be encoded
as follows in our calculus.
\begin{code}
cC, cB, cK, cI, cI', cW, c0 :: E
cC    = V"*" :*: V"^" :^: V"*"             -- M to one plus E to the E 
cB    = V"^" :*: V"*" :^: V"*"             -- M to the C
cK    = V"^" :*: V"0" :^: V"*"             -- 0 to the C
cI    = V"@" :^: V"0"
cI'   = V"^" :*: V"^" :^: V"*"             -- E to the C
cW    = V"^" :*: (V"^" :+: V"^") :^: V"*"  -- twice E to the cC
\end{code}

The `real word' versions:
\begin{code}
combC        = (*) * (^) ^ (*)             --  |flip|, transpose. 
combB        = (^) * (*) ^ (*)             --  |(.)|, composition. |(*) ^ combC| 
combI        = naughtiness ^ (<>)          --  |id|. also |(^) * (^) ^ (*)|, inter alia
combK        = (^) * (<>) ^ (*)            --  |const|. |(<>) ^ combC|
combW        = (^) * ((^) + (^)) ^ (*)     --  diagonalisation. |((^) + (^)) ^ combC|
naughtiness  = error "Naughty!"
\end{code}


As for |S|, after a little playing around, another combinator emerges.  This is |S'|,
where |S a b| (the normal S combinator) is |W (S' a b)|.
\begin{spec} 
    S' a b c1 c2 =    a c1 (b c2)
\end{spec}

It turns out that
\begin{spec}
    S'  =  (*) * ((*) *)
\end{spec}

In particular, we have the following remarkable equations:
\begin{spec}
  S     = S' * (*) * (W ^ (^))
  S'    = S' (*)
  C     = S' (^) 
  B     = S' (^) (*)           = (*) ^ C
  I     = S' (^) (^)           = (^) ^ C
  K     = S' (^) (<>)          = (<>) ^ C
  W     = S' (^) ((^) + (^))   = ((^) + (^)) ^ C
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
cPair = V"^" :*: V"*" :*: (V"^" :^: V"*")
\end{code}

Closely related to pairing is the Curry combinator,
which
satisfies | f^cCurry x y = f (x , y) |.
The following are alternate versions of this combinator.
\begin{code}
cCurry   = cK :*: (cPair :^: cA)
cCurry'  = cB :*: (cPair :^: cM)
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

-- so lets give an alias for left rotation
cL          :: E
cL          = cPair

cR_demo  = test $ vc :^: vb :^: va :^: cR
cL_demo  = test $ vc :^: vb :^: va :^: cL
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

\subsection{Continuation transform}

The function |^| which takes |a| to |a ^| pops up everywhere when playing
with arithmetical combinators.
It provides the basic means of interchanging the positions
of variables:
| a^b = b^(a^) = b^a^(^) |.

On the topic of the continuation transform, for a fixed result type
|R = ()|, the type-transformer |CT|
\begin{code}
type CT a = (a -> ()) -> ()
\end{code}
is the well known continuation monad.
The action on maps is
\begin{code}
map_CT :: (a -> b) -> CT a -> CT b
map_CT f cta k = cta (k . f)
map_CT'1 f cta k = cta (f * k)
map_CT'2 f cta   = (f *) * cta
map_CT' f       = ((f *) *)

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
\fi

You may be interested in fancy control operators (like `abort'), and
flirtations with classical logic.
The following may reduce your cravings.

Peirce's law: | ((a->b) -> a) -> a |
is interesting because it is a formula of minimal logic.
It involves only the arrow, and not |0|.
\emph{Yet} you can prove excluded
middle $a or not a$ from it, where negation is relativised to a generic
type $r$, as |not a = a -> r|.  So when defining something,
one has unrestricted access to these two cases.

Peirce's law postulates the existence of an algebra for
a certain monad, called `the Peirce monad' by Escardo\&co.

When `true' |0| (including efq) and hence true negation is
added, to minimal logic, Peirce's law implies not just
excluded middle, but full classical logic with involutive
negation, \ie{} |~(~A) = A|. 

To suppose the negation of Peirce's law leads
to an absurdity. (We don't need efq for this.)
\begin{spec}
      ~Peirce   =   ~a & ((a->b)->a)
                =>  ~a & ~(a->b)
                =   ~a & ~b & a 
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
ct a       =   a :^: V "^"                     -- unit
cb         ::  E -> E -> E
cb m f     =   V "^" :*: (f :^: V "*") :*: m  -- bind

cCTret, cCTjoin, cCTbind ::  E
cCTret     =   V"^"
cCTjoin    =   cCTret :^: V"*"
cCTbind    =   blog "m" (blog "f" (cb (V"m") (V"f")))
\end{code}
It may be interesting to point out that
$(a,b) = a^{[\wedge]} \times b^{[\wedge]} = \eta a \times \eta b$
where $\eta$ is the unit of CT.


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
cOsuc e = e :+: (e :^: V"^")

cOzero :: E
cOzero = V"0"

cO :: Int -> E    -- allows inputting numerals in decimal.
cO n = let x = cOzero : [cOsuc t | t <- x ] in x !! n 
\end{code}
\subsection{sgbar, \etc{}}


|sgbar|, or exponentiation to base zero, is the function which is 1 at
0, and 0 everywhere else.  In other words, it is the characteristic
function of the zero numbers.  
\begin{code}
sgbar = ((<>) ^)
cSgbar = c0 :^: cE
sgbar' :: EE (N a)
sgbar' n s z = n (const z) (s z)
cSgbar' = let v1 = vz :^: vs
              ef = vz :^: cK
          in (blog "n" (blog "s" (blog "z" (v1 :^: ef :^: vn ))))
\end{code}

Using |sgbar|, we can define |sg|, which is 0
at 0, and 1 elsewhere (the sign function, or the characteristic
function of the non-zero numbers).
\begin{code}
sg = sgbar * sgbar
sg' :: EE (N a)
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

Once used, with |test|, to demo some evaluations.
\begin{code}

demo1Add     = let d = va :+: vb
               in vc :^: d
demo1Zero    = let d = V"0" in va :^: d 
demo1Mul     = let d = va :*: vb in vc :^: d
demo1One     = let d = V"1" in va :^: d

-- show that the logarithm of an exponential behaves as expected
demoExp     = let d = (va :^: cPair) :*: (vb :^: V"^")
              in vc :^: d
demoExp'    = let d = (va :*: cPair) :+: (vb :*: V"^")
              in vd :^: vc :^: d

-- two equivalent codings                 
demoAdd     = let c = (va :^: V"^") :+: (vb :^: V"^") 
                  d = cPair :*: V"*" :*: (c :^: V"^")
              in ve :^: vd :^: vc :^: d
demoAdd'    = let c = (va :^: V"^") :+: (vb :^: V"^")
                  d = cPair :+: (c :^: cK)
              in ve :^: vd :^: vc :^: d

demoNaught  = let d = V"0" :*: V"0" :^: V"^" in d
\end{code}
%\fi
\end{document}

Safe place for debris:

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
 test $ vx :^: ((va :^: cPair) :*: (vb :^: V"^"))
--demonstrates that a ^ b = a ^ cPair :*: b ^ cE
\fi
