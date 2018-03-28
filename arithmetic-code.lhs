A Turing complete arithmetical calculator.

Some haskell boilerplate. We are going to play around with
the ordinary arithmetical symbols, and versions of these
symbols in angle-brackets eg. |<+>|.
\begin{code} 
module Arithmetic where 
import Data.Char
import Prelude hiding --
               ((*),(^),(+),(<>)
               ,(<*>),(<^>),(<+>),(<<>>)
               ,(:^:),(:*:),(:+:),(:<>:))
infixr 8  ^ 
infixr 7  *  
infixr 6  +  
infixr 9  <>

main :: IO ()        -- Do something with this later.
main =  putStrLn
          "Load in ghci and type something like \"test $ vc :^: vb :^: va :^: cC"  
\end{code}

\section{The real-world arithmetical combinators}

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
\end{code}

The type-schemes inferred for the definitions are as follows:
\begin{code}
(^)      :: a -> (a -> b) -> b
(*)      :: (a -> b) -> (b -> c) -> a -> c
(+)      :: (a -> b -> c) -> (a -> c -> d) -> a -> b -> d
(<>)     :: a -> b -> b
one      :: a -> a
\end{code}


The defining equations above generate an equivalence relation between
(possibly open) terms in a signature with eight operators:

* 4 constants (^), (*), (+) and (<>)
* 4 binary operators _^_, _*_, _+_ and _<>_

This is the least equivalence relation
extending the definitions, congruent to all operators in the signature.  
This means that equations between open terms can be proved by
substituting equals for equals.

One can also allow instances of the following ``$\zeta$-rule'' in proving equations.
\begin{center}
    \begin{tabular}{c} |x ^ a = x ^ b|  $\mbox{}\ruleimplies\mbox{}$ |a = b| \end{tabular}
\end{center}
with the side condition that |x| is fresh to both |a| and |b|.

The $\zeta$-rule is an expression of `exponentiality':
two values that behave the same as exponents of a generic base are the very same value.
I shall call this relation $\zeta$-equality.  Any equation I assert
should be interpreted as $\zeta$-equations, unless I say otherwise.
 
\section{Arithmetical calculus}

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
data E  = V String | E :^: E | E :*: E | E :+: E | E :<>: E 
          deriving  (Eq) -- (Show,Eq) 
\end{code}

We can think of these expressions as fancy Lisp S-expressions, with four
different binary `cons' operations, each with an distinct arithmetical flavour.


It is convenient to have atomic constants identified by arbitrary strings.
The constants |"+"|, |"*"|, |"^"|, |"0"| and |"1"| are treated specially.
\begin{code}
(cA,cM,cE,c0,c1) = (V"+",V"*",V"^",V"0",V"1")
\end{code}

For each arithmetical operator, we define a function that takes two
arguments, and (sometimes) returns a `normal' form of the expression 
formed with that operator.  (This doesn't allow us to trace reduction
sequences -- we turn to that later.) The definitions correspond to the
transitions of an arithmetical machine. 

\begin{code}
infixr 9  <<>>
infixr 8  <^> 
infixr 7  <*>
infixr 6  <+>
\end{code}

\begin{code}
(<+>),(<*>),(<^>),(<<>>) :: E -> E -> E
a <+> b = case a of  V "0"         -> b
                     _             -> case b of  V "0"         -> a
                                                 b1 :+: b2     -> (a <+> b1) <+> b2
                                                 _             -> a :+: b 
a <*> b = case a of  _ :^: V "0"   -> b
                     _             -> case b of  V "0"         -> b
                                                 b1 :+: b2     -> (a <*> b1) <+> (a <*> b2)
                                                 b1 :*: b2     -> (a <*> b1) <*> b2
                                                 _  :^: V "0"  -> a
                                                 _             -> a :*: b 
a <^> b = case b of  V "0"         -> b :^: b 
                     b1 :+: b2     -> (a <^> b1) <*> (a <^> b2)
                     b1 :*: b2     -> (a <^> b1) <^> b2
                     _  :^: V "0"  -> a
                     b1 :^: V "^"  -> b1 <^> a   -- note: destroys termination
                     b1 :^: V "*"  -> b1 <*> a
                     b1 :^: V "+"  -> b1 <+> a
                     b1 :^: b2     -> a :^: (b1 <^> b2) 
                     _             -> a :^: b 
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
of an expression (with respect to some rewriting rules hard-wired in the code)
if one exists. (Otherwise it will probably hang, or consume all the memory
in your computer.)
Such an evaluator may let us see the value an expression has, but it doesn't 
show how this was arrived at.

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
             (a :+: (b :+: c))   ->  [ (a :+: b) :+: c         ] -- space reuse
             (V "0" :+: a)       ->  [ a                       ] -- drop1
             (a :+: V "0")       ->  [ a                       ] -- drop1
             (a :*: (b :+: c))   ->  [ (a :*: b) :+: (a :*: c) ] -- 2 -> 3
             (a :*: V "0")       ->  [ c0                      ] -- drop1
             (a :*: (b :*: c))   ->  [ (a :*: b) :*: c         ] -- reuse
             (V "1" :*: a)       ->  [ a                       ] -- drop1
             (a :*: V "1")       ->  [ a                       ] -- drop1
             (a :^: (b :+: c))   ->  [ (a :^: b) :*: (a :^: c) ] -- 2 -> 3
             (a :^: V "0")       ->  [ c1                      ] -- drop1
             (a :^: (b :*: c))   ->  [ (a :^: b) :^: c         ] -- reuse
             (a :^: V "1")       ->  [ a                       ] -- drop1
             (a :^: b :^: V "+") ->  [ b :+: a                 ] -- drop1
             (a :^: b :^: V "*") ->  [ b :*: a                 ] -- drop1
             (a :^: b :^: V "^") ->  [ b :^: a                 ] -- drop1
             (a :^: b :^: V "0") ->  [ b :<>: a                ] -- drop2  b :<>: a
             (a :<>: b)          ->  [ b                       ] -- drop1
             _                   ->  [                         ]
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
                       h op a b
                         =  l ++ r where  l  = [ ((a `op`) . f,p) | (f,p) <- sites b ]  -- right operand b first
                                          r  = [ ((`op` b) . f,p) | (f,p) <- sites a ]
\end{code}
It should be noted that "far-right" sites have priority. This is just a mirror image of the
normal situation, where the first argument comes first.

Now we define for any expression a list of the expressions to which it
reduces in a single, possibly internal step, at exactly one site 
in the expression.  This uses the function |tlr| to get
top-level reducts. 

\begin{code}
reducts :: E -> [ E ]
reducts a     = [ f a'' | (f,a') <- sites a, a'' <- tlr a' ]
\end{code}

\subsection{holding reduction sequences in a tree}

We need a structure to hold the reduction sequences from an
expression.  So-called `rose' trees , labelled by expressions seem ideal.

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

Putting things together, we can map an expression to its
a sequence of its reduction sequences. 
\begin{code}
rss :: E -> [[E]]
rss = branches . reductTree
\end{code}

Usually it is the first `canonical' reduction sequence of interest.

\end{document}

\section{B{\"o}hm's logarithms}

This code is concerned generating the logarithm of an expression
with respect to a variable name.

B{\"o}hm's combinators
\begin{code}
cBohmA a b = let g = a :^: V"^" :+: b :^: V"^" in 
             let t = cPair :+: g :^: cK in   -- Bohm's original
             let t' = cPair :*: V"*" :*: (g :^: V"^")  -- another without additive apparatus 
             in t'
cBohmE a b = a :*: cPair :+: b :*: V"^"
cBohmM a b = a :+: b              
cBohm0 a   = V"0" :*: a :^: V"^"
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

\section{Bureaucracy and basic gadgetry}

To save typing, some names for variables
\begin{code}
( va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk, vl, vm, vn,
  vs, vt, vu, vv, vw, vx, vy, vz) 
  = ( V"a", V"b", V"c", V"d", V"e", V"f", V"g", V"h", V"i", V"j", V"k", V"l", V"m", V"n"
    , V"s", V"t", V"u", V"v", V"w", V"x", V"y", V"z")
\end{code}

We code a few useful numbers as expressions.
\begin{code}
c2, c3, c4 , c5, c6, c7, c8, c9, c10 :: E
c2       = c1      :+: c1
c3       = c2      :+: c1 
c4       = c2      :^: c2
c5       = c2      :+: c3
c6       = c3      :*: c2
c7       = c3      :+: c4
c8       = c2      :^: c3
c9       = c3      :^: c2
c10      = c2      :*: c5
\end{code}
|c0| and |c1| have already been defined.

\section{Displaying}

\subsection{expressions} 
    
If one wants to investigate reduction sequences of arithmetical
expressions by running this code, one needs to display them.
To display expressions, we use the following code,
which is slightly less noisy than the built in show instance.
It should supress parentheses with associative operators.
(I think everything is right associative: as with ^, so
with the other operators.)
I write the constant combinators in square brackets, which may
be considered noisy.

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
showE (V str) _ = (str++)
showE (a :+: b) p = opp p 0 (showE a 0 . (" + "++) . showE b 0)
showE (a :*: b) p = opp p 2 (showE a 2 . (" * "++) . showE b 2)
showE (a :^: b) p = opp p 4 (showE a 5 . (" ^ "++) . showE b 4)
showE (a :<>: b) p = opp p 4 (showE a 5 . (" ! "++) . showE b 4)
parenthesize f = showString"(" . f . showString")"
opp p op = if p > op then parenthesize else id 
\end{code}

\begin{code}
instance Show E where showsPrec _ e = showE e 0 
\end{code}


\subsection{trees and lists} 

Code to display an |NTree a| that indentation in an attempt to make the
branching structure of the tree visible. (Actually, this is entirely useless.)
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

Code to display a numbered list of showable things, throwing a line between entries.
\begin{code}
newtype NList a = NList [a]
instance Show a => Show (NList a) where
   showsPrec _ (NList es) = 
      (composelist . commalist ('\n':) . map showline . enum ) es
      where showline (n,e) = shows n . showString ": " . shows e 
\end{code}
 
Code to pair each entry in a list with its position.
\begin{code}
enum :: [a] -> [(Int,a)]
enum = zip [1..]
\end{code}

\begin{code}
composelist :: [ a -> a ] -> a -> a
composelist = foldr (.) id
\end{code}

Code to insert a `comma' at intervening positions in a list.
\begin{code}
commalist :: a -> [a] -> [a]
commalist c (x:(xs'@(_:_))) = x:c:commalist c xs' 
commalist c xs = xs
\end{code}

\begin{code}
nodups [] = []
nodups (x:xs) = x : nodups (filter (/= x) xs)
\end{code}

\subsection{Some interesting things to use}

The first reduction sequence. This is by far the most useful. One might type something like
\begin{spec}
         test $ vu :^: vz :^: vy :^: vx :^: cS
\end{spec}
and see in response:
\begin{spec}
1: u ^ z ^ y ^ x ^ ((*) * (*) ^ (*) * ((^) * ((^) + (^)) ^ (*)) ^ ((^) * (*) ^ (*)))
2: u ^ z ^ y ^ (x ^ ((*) * (*) ^ (*))) ^ ((^) * ((^) + (^)) ^ (*)) ^ ((^) * (*) ^ (*))
3: u ^ z ^ y ^ (x ^ ((*) * (*) ^ (*))) ^ (((^) * ((^) + (^)) ^ (*)) ^ (^)) ^ (*) ^ (*)
4: u ^ z ^ y ^ (x ^ ((*) * (*) ^ (*))) ^ ((*) * ((^) * ((^) + (^)) ^ (*)) ^ (^))
5: u ^ z ^ y ^ ((x ^ ((*) * (*) ^ (*))) ^ (*)) ^ ((^) * ((^) + (^)) ^ (*)) ^ (^)
6: u ^ z ^ y ^ ((^) * ((^) + (^)) ^ (*)) ^ (x ^ ((*) * (*) ^ (*))) ^ (*)
7: u ^ z ^ y ^ (x ^ ((*) * (*) ^ (*)) * (^) * ((^) + (^)) ^ (*))
8: u ^ z ^ (y ^ x ^ ((*) * (*) ^ (*))) ^ ((^) * ((^) + (^)) ^ (*))
9: u ^ z ^ ((y ^ x ^ ((*) * (*) ^ (*))) ^ (^)) ^ ((^) + (^)) ^ (*)
10: u ^ z ^ (((^) + (^)) * (y ^ x ^ ((*) * (*) ^ (*))) ^ (^))
11: u ^ (z ^ ((^) + (^))) ^ (y ^ x ^ ((*) * (*) ^ (*))) ^ (^)
12: u ^ (y ^ x ^ ((*) * (*) ^ (*))) ^ z ^ ((^) + (^))
13: u ^ (y ^ x ^ ((*) * (*) ^ (*))) ^ (z ^ (^) * z ^ (^))
14: u ^ ((y ^ x ^ ((*) * (*) ^ (*))) ^ z ^ (^)) ^ z ^ (^)
15: u ^ z ^ (y ^ x ^ ((*) * (*) ^ (*))) ^ z ^ (^)
16: u ^ z ^ z ^ y ^ x ^ ((*) * (*) ^ (*))
17: u ^ z ^ z ^ y ^ (x ^ (*)) ^ (*) ^ (*)
18: u ^ z ^ z ^ y ^ ((*) * x ^ (*))
19: u ^ z ^ z ^ (y ^ (*)) ^ x ^ (*)
20: u ^ z ^ z ^ (x * y ^ (*))
21: u ^ z ^ (z ^ x) ^ y ^ (*)
22: u ^ z ^ (y * z ^ x)
23: u ^ (z ^ y) ^ z ^ x
\end{spec}

\begin{code}
test :: E -> NList E
test  = NList . hd . rss 
hd (x:_) = x 
\end{code}


The n'th reduction sequence.

\begin{code}
nth_rs :: Int -> E -> NList E 
nth_rs n = NList . (!! n) . rss 
\end{code}


Some basic stats on reduction sequence length. The number
of reduction sequences, and the extreme values of their lengths.
Be warned, this can take a very long time to finish on
even quite small examples. 
\begin{code}
stats_rss :: E -> (Int,(Int,Int))
stats_rss e = let (b0:bs) = map length (rss e)
              in (length (b0:bs), ( foldr min b0 bs , foldr max b0 bs) )
\end{code}

\begin{code}
nf :: E -> [E]
nf = map last . rss 

fd :: [E] -> Maybe (E,[E])   -- first difference
fd [] = Nothing
fd [x] = Nothing
-- fd (x:xs) = let e = [t | t <- xs, t /= x]
--            in if e == [] then Nothing else Just (x,e)
fd (x:xs@(y:_)) | x == y = fd xs
fd (x:xs@(y:_)) | x /= y = Just (x, xs)

\end{code}





%\appendix
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
combC = (*) * (^) ^ (*)             -- |flip|, transpose. 
combB = (^) * (*) ^ (*)             -- |(.)|, composition. |(*) ^ combC| 
combI = naughtiness ^ (<>)                 -- |id|. also |(^) * (^) ^ (*)|, inter alia
combK = (^) * (<>) ^ (*)            -- |const|. |(<>) ^ combC|
combW = (^) * ((^) + (^)) ^ (*)     -- diagonalisation. |((^) + (^)) ^ combC|
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
The floowing are alternate versions of this combinator.
\begin{code}
cCurry = cK :*: (cPair :^: V"+")
cCurry' = cB :*: (cPair :^: cM)
\end{code}

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
cTrue = V"0" :^: cC
cFalse = V"0"
\end{code}

\begin{spec}
fst p    = p tru 
         = tru ^ p 
         = p^(tru^)
fst      = (tru^)
snd      = (fal^)
\end{spec}

\begin{code}
cFst = cTrue :^: V"^" 
cSnd = cFalse :^: V"^"
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
cR, cR'     :: E
cR          = cC :^: cC 
cR'         = (V "^") :*: (V "^") :*: (V "*") :^: (V "*")
\end{code}

It so happens that the |cC| combinator and the |cR| are each
definable from the other. 

\begin{spec}
  cR :^: cR :^: cR = cC 
  cC :^: cC        = cR              
\end{spec}

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
|R|, the type-transformer |CT|
\begin{spec}
 CT a = (a -> R) -> R
\end{spec}
is the well known continuation monad.  The unit |return| and multiplication |join| 
of this monad have simple arithmetical expressions. 
\begin{spec}
return :: a -> CT a
join   :: CT (CT a) -> CT a
return a b = a ^ b       -- ie. |return = (^)|
f `join` s = f (return s)     -- ie. |join = ((^)*)|
\end{spec}

TODO: Is this for real?
The bind operator |>>=| is not quite as simple.
\begin{spec}
 m >>= f = m . (f^C)
         = (f^C) * m 
         = (^) * (f*) * m
 (>>=)^C f m = (^) * (f*) * m
 (>>=)^C f   = ((^)*) . ((f*)*)
             = ((f*)*) * ((^)*)
 f^((>>=)^C) = ((f^(*))^(*) * (^)^(*)
 (>>=)^C     = (*)*(*)*(((^)^(*))^B)
 (>>=)^C     = (*)*(*)*(^)^((*)*B)
 (>>=)       = ((*)*(*)*(^)^((*)*B))^C
\end{spec}

You may interested to see what |callCC| looks like.  That's
the function whose type is the Kleislified version of 
Peirce's law:  |((a -> CT b) -> CT a) -> CT a|. Unless I'm
missing something, it is not very beguiling:
\begin{spec}
(((*) * ((^) * 0 ^ (*)) ^ (^)) ^ (*) * (^)) * ((^) + (^)) ^ (*)
\end{spec}
Well, that's classical logic for you.

The monadic apparatus can be encoded as follows
\begin{code}
ct         :: E -> E
ct a       = a :^: V "^"                     -- unit
cb m f     = V "^" :*: (f :^: V "*") :*: m  -- bind
\end{code}



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
          = b^(((<>)^) + (1^) + ... + ((n-2)^) + ((n-1)^) 
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
\begin{spec}
  0  = {}
  1  = {{}}
  2  = {{},{{}}}
  3  = {{},{{}},{{},{{}}}}
  ...
\end{spec}
Clearly the operation of raising to the power of exponentiation (that
takes |n| to |(n^)|) plays the role of the singleton operation  $n \mapsto \{n\}$.


\subsection{sgbar}


|sgbar|, or exponentiation to base zero, is the function which is 1 at
0, and 0 everywhere else.  In other words, it is the characteristic
function of the zero numbers.  
\begin{code}
sgbar = ((<>) ^)
\end{code}

Using |sgbar|, we can define |sg|, which is 0
at 0, and 1 elsewhere (the sign function, or the characteristic
function of the non-zero numbers).
\begin{code}
sg = sgbar * sgbar 
\end{code}
It may be clearer to write it |sg a = (<>) ^ (<>) ^ a|.  Think of double negation. 

Using |sg| and |sgbar|, we can implement a form of boolean
conditionals.  | IF b=0 THEN a ELSE c | 
can be defined as | a*sg(b)+c*sgbar(b) |.  

In fact we have forms of definition by finite cases.


\iffalse
\subsection{A simple parser}

Is it even worth thinking about this?  The interpreter gives a
fine language for defining expressions, using let expressions, etc.

Something changed in ghc 7.10.2 making it a fuss to write simple parsers.
Applicative is bound up with monads, and they have stolen |<*>|. If
I hide that, I hide monads, and can't use do notation. 

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


-- SCANNER.
-- turns a stream of characters into a stream of tokens.

-- import Data.Char

is_alphabetic c = 'a' <= (c :: Char) && c <= 'z' || 'A' <= c && c <= 'Z'
is_digit      c = '0' <= (c :: Char) && c <= '9' 
is_idchar     c = c `elem` "_." || is_alphabetic c || is_digit c 
is_space      c = c == ' '
is_par        c = c `elem` "()"
is_symch      c = not (is_par c || is_space c)

data Tok = Id String | Num Int |
           Sym String | Lpar | Rpar
           deriving (Show,Eq)
tokens :: String -> [Tok]
tokens [] = []
tokens (c:cs) | isSpace c = tokens cs
tokens (inp@('(':cs)) 
          = Lpar : tokens cs
tokens (inp@(')':cs)) 
          = Rpar : tokens cs 
tokens (c:cs) | is_alphabetic c
          = id_t (c:) cs where
                id_t b [] = [Id (b [])]
                id_t b (c:cs) | is_idchar c = id_t (b . (c :)) cs
                id_t b inp         = Id (b []): tokens inp 
tokens (c:cs) -- | is_symch c 
          = id_t (c:) cs where
                id_t b [] = [Sym (b [])]
                id_t b (c:cs) | is_symch c = id_t (b . (c :)) cs
                id_t b inp               = Sym (b []): tokens inp 

{- damn it! I have pinched * and + for a more general purpose.
tokens (inp@(c:cs)) | is_digit c
          = id_t (vd c) cs where
                id_t b [] = [Num b]
                id_t b (c:cs) | is_digit c = id_t (b * 10 + ord c) cs
                id_t b inp               = Num b : tokens inp
                vd = digitToInt
-}


-- GRAMMAR

variable :: Parser Tok E
variable = Parser p where
            p (Id st : ts) = [(V st,ts)]
            p _            = []

constant :: Parser Tok E
constant = Parser p where
            p (Sym st : ts) = [(V st,ts)]
            p _            = []

atomic         = variable `alt` constant `alt` paren expression
additive       = Parser (\s-> [ (fo (:+:) x xs ,s')
                              | ((x:xs),s') <-
                                   prun (repsep multiplicative (lit (Sym "+"))) s ])
multiplicative = Parser (\s-> [ (fo (:*:) x xs ,s')
                              | ((x:xs),s') <-
                                   prun (repsep exponential (lit (Sym "*"))) s ])
exponential    = Parser (\s-> [ (fo (:^:) x xs ,s')
                              | ((x:xs),s') <-
                                   prun (repsep atomic (lit (Sym "^"))) s ])
expression     = additive

-- foldr1 ? 
fo op fst [] = fst
fo op fst (x:xs) = fst `op` fo op x xs 

-- instance Read E where
--  readsPrec d = prun expression . tokens

\end{code}


Some terms to explore:
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
\iffalse
 test $ vx :^: ((va :^: cPair) :*: (vb :^: V"^"))
--demonstrates that a ^ b = a ^ cPair :*: b ^ cE
\fi
\fi
\end{document}


*Main> let l = V"*" :*: cB :*: (V"+" :^: V"*") ; r = V"*" :+: (V"+" :^: cK) :+: (V"*" :*: V"*") in test (vc :^: vb :^: va :^: l)

  let sb = (vc :^: vb) :^: vc :^: va ; s = blog "a" (blog "b" (blog "c" sb)) ; k = blog "a" (blog "b" va) in test $ vw :^: vz :^: vy :^: vx :^: s
