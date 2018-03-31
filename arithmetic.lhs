\documentclass{article}
\usepackage{graphicx}
\usepackage{color}
\usepackage[usenames,dvipsnames,svgnames,table]{xcolor}
\usepackage[colorlinks=true,
            linkcolor=red,
            urlcolor=blue,
            citecolor=gray]{hyperref}
%\usepackage[colorlinks=true,citecolor=gray]{hyperref}
\usepackage{gensymb}
\usepackage{varioref}

\providecommand{\dotdiv}{% Don't redefine it if available
  \mathbin{% We want a binary operation
    \vphantom{+}% The same height as a plus or minus
    \text{% Change size in sub/superscripts
      \mathsurround=0pt % To be on the safe side
      \ooalign{% Superimpose the two symbols
        \noalign{\kern-.45ex}% but the dot is raised a bit
        \hidewidth$\smash{\cdot}$\hidewidth\cr % Dot
        \noalign{\kern.45ex}% Backup for vertical alignment
        $-$\cr % Minus
      }%
    }%
  }%
}
% Time-stamp: 2015-08-28 06:16:35 pgh
% \title{AMEN: The last word in combinators \\ (A Naperian meditation)}
\title{The `AMEN' combinators: arithmetic, algebra, Naperiana}
\title{Tractatus logarithmico-arithmeticus\\ (the Naperian combinators)}
%
%%%%\dedication{Dedicated to Conor McBride}
%A Naperian take on $\lambda$} 
\author{Peter Hancock}
%\date{{\Huge \textbf{DRAFT}} of August 21, 2008}
\date{\today}
\input{preamble.tex}

%include polycode.fmt
%format <> = "\!\mathop{{}^{{}^{\cdot}}}\!"
%format ^ = "\wedge"
%format ** = "**"
%format * = "\times"
%format :+: = ":\!+\!:"
%format :^: = ":\!\wedge\!:"
%format :*: = ":\!\times\!:"
%format <^> = "\langle\wedge\rangle"
%format <*> = "\langle\times\rangle"
%format <+> = "\langle+\rangle"
%format <<!>> = "\langle\!\mathop{{}^{{}^{\cdot}}}\!\rangle"
%format alpha = "\alpha"
%format beta = "\beta"
%format gamma = "\gamma"
%%format "^" = "\"\wedge\""
%format LEQ = "\leq" 
%format <=> = "\iff"
%format chipmul = "\mathop{\setminus}" 
%format chopmul = "\mathop{/}"
%format chipadd = "\mathop{-\!\!<}"
%format chopadd = "\mathop{>\!\!-}"
%format b0 = " b_0"
%format b1 = " b_1"
%format b2 = " b_2"
%format bk = "b_k"
%format bn = " b_n"
%format k0 = " k_0"
%format k1 = " k_1"
%format k2 = " k_2"
%format kn = " k_n"
%%format c0 = " c_0"
%format c1 = " c_1"
%format c2 = " c_2"
%format cn = " c_n"
%format CW = " W^C "
%format Omega = "\Omega"
%format omega = "\omega"
%format sum = "\mbox{$\sum$}"
%format prod = "\mbox{$\prod$}"
%format STOP = "\hspace{1em}."
%format COMMA = "\hspace{1em},"
%%%%%%%%%%%%%%%%%%%%%%%\Usepackage{mathlig}
\newcommand{\ZERO}{\ensuremath{{\!\mathop{{}^{{}^\cdot}\!}}}}
\newcommand{\COMMA}{\ensuremath{{{\!}\mathop{{\mbox{,}}}}}}
\newcommand{\DOT}{\ensuremath{\cdot}} %{\mathbin{{\!}{\makebox[1em][c]{.}}}}}}
\newcommand{\curry}{\ensuremath{\mathit{curry}}}

\begin{document}
\maketitle
\hypersetup{linkcolor=red}
\tableofcontents
\hypersetup{linkcolor=blue}
\listoffigures
\hypersetup{linkcolor=blue}

\begin{abstract}

The $\lambda$-calculus, typed or not, has a little-known arithmetical aspect.
We arrive at it by considering application, exponentiation and even iteration
to be the essentially the same operation.

The first indication that this might make sense is
the coincidence between
superscript notation $f^n$ for iteration,
which applies the exponent or iterator $n$ to unary operation $f$, and $m^n$ for exponentiation.  As Wittgenstein said, a number is an exponent of an operation.

This brings in its train a set of `AMEN' combinators
for addition,
multiplication, exponentiation and naught (zero) of Church-numerals.
They have some some useful algebraic properties (in
the presence of the $\zeta$-rule).  Moreover, they are combinatorially complete,
in that they support a certain notion of `logarithm',
consistent with but extending some of Napier's
laws of logarithms.

The interest of logarithms (to a `variable' base!) seems to be originally pointed out and explored
by B{\"o}hm in the late 1970's,
in some undeservedly little-known papers from that time.  
His arithmetic and algebra of combinators has great entertainment value.
But there is some intellectual value in B{\"o}hm's arithmetical ruminations,
that I think bears some repeating. 

%The basic idea is quite simple, and far from new. (It can be traced back to
%the 1920's, combinatorial completeness was not unknown in the 1960's,
%and the algebraic (and logarithic!) structure was  investigated principally by B{\"o}hm in the 1970's.) 

\end{abstract}
%\tableofcontents
%%%%%%%%%%%%%%%%%%%%%%%\input{ligatures.tex}


\section{Introduction}

%\paragraph{Recent attempt Thu May 24 09:28:24 BST 2007  to write an intro}\mbox{}


What are numbers?  Leaving aside the numbers we use when measuring things, specifically, what are the numbers we use
when we are counting off operations, as when giving someone
change for something bought in a shop, or playing the drums?
The answer is that numbers are fundamentally iterators,
or templates for keeping track of iterations.

Something similar can be said about elements of any initial algebra.
The natural numbers are just a particularly simple case.

The idea of iteration carries within it the idea of exponentiation, or raising one number to the power of another.
An iterator $a$ takes an endofunction $f : X \to X$ on a set $X$,
and gives back its $a$-th iterate $f' : X \to X$, and so is itself an endofunction (on $X \to X$) that can be iterated, say $b$ times.
This takes $f : X \to X$ to $f \wedge (\exp_{a} b)$, and indeed $(+1) : X \to X$ and $o : X$ to $o + a^b$. 
Exponentiation $b^e$ is itself a form of iteration: it is iterated multiplication by $b$ (ie. $(\times b)$), starting at $1$.

Exponential notation for numbers is at least as old as Archimedes, who considered
the problem of counting or estimating immensely many grains of sand.
He devised an exponential notation in which
he expressed an upper bound for the number of grains it would take to 
fill the universe.  

Numbers are among the first abstract things to which we give names, and notation.
A handly notation for iteration
%that is often handy to eliminate clutter
is superscription, writing the number
of iterations as a superscript of the expression for the iterated operation $f$
\[
               f^n
\]
It is not an accident that we often use the same superscription notation for numerical
exponentiation, with the base replacing the operator, and the
exponent replacing the iteration
\[
\begin{array}{lcl}
               b^e  &=& (\times b)^e(1) \\
               b\times e  &=& (+ b)^e(0) \\
               b + e  &=& (+ 1)^e(b)
\end{array}
\]
In these equations, the first superscription denotes numerical exponentiation,
and the others denote iteration.

Superscripts can soon get out of hand
at about 2 levels of nesting, so in practice one needs a 
infix binary operator such as |b ^ e|.  Still, superscription is sometimes
helpful in helping to read expressions without undue parenthetical
clutter, and take in their grammatical structure.  So I'll often use superscription
(particularly when the exponent expression is simple) as well as the infix operator, 

What this paper is about is the 
use of exponential notation for function application itself,
but with the function as the right operand. 
Hand in hand with exponential notation comes
a useful algebraic calculus (`exponential calculus', or Cantor's laws of exponents) involving
the operators $\times$, %|.|, 
$1$, $+$ and $0$ for working with
exponential notation:
\[
\begin{array}{llllllllll}
          c^{a \times  b} &= (c^a)^b         &&& a^1 &= a \\
          c^{a +       b} &= c^a \times c^b  &&& a^0 &= 1 \\ 
\end{array}
\]
A certain part of this calculus, 
may be re-expressed in terms of logarithms to an `indeterminate' base $x$::
\[
\begin{array}{llllllllll}
          {(\log_x b) \times  c} &= \log_x (b^c)         &&& 1 &= \log_x x \\
          {\log_x b + \log_x c} &= \log_x (b \times c)  &&& 0 &= \log_x 1 \\
\end{array}
\]
If one thinks of application as raising the argument to the power of the function, then
surely some form of $\lambda$-abstraction, or `bracket abstraction' should correspond to
the logarithm.  This is indeed the case, as originally shown by B{\"o}hm over 3 decades ago,
to be re-presented in section \vref{sec:log}.


\section{The AMEN combinators: $+$, $\times$, $\wedge$, $0$.}

We can read Cantor's laws as \emph{defining}
combinators |(*)|,|1|,|(+)|,|0|, using
superscript ($a^f$) or exponential ($a \wedge f$) notation for application, instead
of applicative $f(a)$ notation, as in various Haskell notations like |f a| or |f $ a|.

In this notation the binary operators are related to the combinators by the 
arithmetically mind-boggling laws:
\begin{spec}
  b ^ c      =  c ^ b  ^ (^) 
  b * c      =  c ^ b  ^ (*) 
  b + c      =  c ^ b  ^ (+) 
\end{spec}

\iffalse
Remarkably, these combinators (minimally  |(*)|,|(+)|,|(^)| and |0|) turn out to be
combinatorially complete.  Just like the fairly well-known
pair |S, K|, or the less well-known set |C, B, K, W|,
(or indeed a large variety of other sets of combinators)
they are a sufficient basis for introducing 
$\lambda$-abstraction |\ x -> e| as meta-notation for a certain combinatory expression, where |e| is an arithmetical %exponential
expression with at most one free variable |x|.  Formally, this strongly
resembles `logarithm to the base $x$'. It % has to
satisfies the 
$\beta$-rule\footnote{Sometimes called cancellation.} |a ^ (\ x -> b) = [x<-a]b| 
where |b| may contain occurrences of the free variable |x|, but |a| must not. 
Here |[x<-a]| is the operation of substituting |a| for |x| in a combinatory expression.
It also satisfies the so-called $\eta$-law\footnote{Sometimes called reflection.} |(\ x -> x ^ a) = a| where |a| is closed.) 
 


% The logarithm fits well
% with this exponential calculus
% \[
% \begin{array}{lllllllll}
%           (\log_a b)  \times  c &= \log_a (b^c)    &&& 1 &= \log_a a \\
%           (\log_a b) + (\log_a c) &= \log_a (b \times c)  &&& 0 &= \log_a 1 
% \end{array}
% \]
%  This turns out to be so, at least for \emph{linear}\footnote{Technically, \emph{affine}.}lambda abstraction, where
% there may be at most one occurrence of the bound variable in the body.  But, it holds even more
% generally, as shown by the equation above for
% the logarithm of a product.

\fi



\iffalse
Agreeably, the arithmetical notation meshes well with notions of
linearity.  The fragment |(^), (*), (<>)| without addition
characterises the affine lambda calculus, and if we also throw out
naught~\footnote{ I use old-fashioned spelling ``naught'': the word is
  in fact etymologically connected with ``naughty''.  A lot of 
  fairly salacious word-play in Shakespeare's plays is based on this. It amuses me that the
  concept of zero was thought to be ``dangerous Saracen magic'' in
  medieval times (William of Malmesbury).  According to John Donne,
  ``The less anything is, the less we know it: how invisible,
  unintelligible a thing is nothing''. It Noths, according to Heidegger.  
  % I think I remember Harold
%   Simmons suggesting that the symbol for zero was chosen to be a
%   circle because it is through a circle that we emerged into the
%   world.  
  %If you prefer, 
   We may think of its symbol as the first letter of
  `Origin'.}  itself (but retain |(^), (*), 1 = (<>)^(<>)|) we get the
linear lambda calculus.
\fi

\iffalse
On the aesthetic side, the resulting programs resemble a four-letter genetic
code. (With lots of irritating single parentheses.)  If on the other
hand one uses Haskell's section notation, programs in combinatory form
resemble illusions caused by a serious eye disease, the ultimate in obfuscation.
If I get round to it I will make a postcript picture of a large one, in figure \ref{fig:eye}.
\begin{figure}
\begin{center}
\includegraphics[scale=0.3]{Picture.pdf}. 
\end{center}
\caption{An advanced form of eye disease.}
\label{fig:eye}
\end{figure}
\fi





It is one of the very nice features of Haskell that we can take over
and redefine symbols such as for the arithmetical operations |(+)|,
|(*)|, and |(^)|.  Three (out of four) cheers for the `hiding'
keyword!  However, it doesn't seem that we can take over `|0|'.
\footnote{(PS: It seems that sufficiently advanced ghc-specific voodoo %using ghc with the '-fno-implicit-prelude' flag
exists that one can actually extricate `|0|' from ghc's gullet, and treat it
as an bona-fide identifier. I have not found an opportunity to try. }
This is a slight pity, as it is the only other symbol I need.
I have type-set it here as a dot that is almost invisible: with brackets around it looks
like a squashed `0'.



%-- import Prelude(Show,ShowS,shows,Read,(&&),(||),flip,(.), error,IO,elem,(==),(/=),length,concat,readsPrec,(++),Bool(True,False),Char,(<=),IO,not,zip,foldr,(!!),Int,map,reverse,showString,Eq,String,(>),id,showsPrec)
%-- import Prelude as P hiding ((*),(^),(+),(<*>))

\begin{code} 
module Main where 
import Prelude hiding ((*),(^),(+),(<>),(<*>),(<^>),(<+>),(<<!>>))
infixr 8  ^  
infixr 7  *  
infixr 6  +  
infixr 9  <>     -- yes, there is a symbol there.
\end{code}

Here are some simple definitions of binary operations corresponding to the 
arithmetical combinators: 
\begin{code}
a ^ b  = b a
a * b  = \c -> (c ^ a) ^ b
a + b  = \c -> (c ^ a) * (c ^ b)
(<>) a b = b          -- Written infix, |a `naught` b = b| the operator would be invisible.
\end{code}

Instead of |naught|~\footnote{ I use old-fashioned spelling ``naught'': the word is
  in fact etymologically connected with ``naughty''.  A lot of 
  fairly salacious word-play in Shakespeare's plays skates around this. It amuses me that the
  concept of zero was thought to be ``dangerous Saracen magic'' in
  medieval times (William of Malmesbury).
  According to John Donne,
  ``The less anything is, the less we know it: how invisible,
  unintelligible a thing is nothing''. It Noths, according to Heidegger.  
  % I think I remember Harold
  %   Simmons suggesting that the symbol for zero was chosen to be a
  %   circle because it is through such a circle that we emerged into the
  %   world.  
  %If you prefer, 
   I think of its symbol as the first letter of
  `Origin'.},
I have used the almost unnoticable symbol `|<>|' as an an infix operator, on the grounds
that in prefix form `|(<>)|' it looks
a little like `|0|'.
It throws away its left argument, and returns its right. 
\begin{code}
naught = (<>)
\end{code}

The type-schemes\footnote{
Almost certainly some citable publication contains a Hilbert-style axiomatisation of
propositional logic of the conditional |(->)| equivalent to these type-schemes, at least
modulo permutating the antecedents of a conditional.

Of course it is not uncommon to use exponential and other arithmetic notation at the level of types,
which amounts to an arithmetic of cardinals.
But such a precious notational device as exponentiation should not be too heavily overloaded.
}
 inferred for the definitions are as follows:
\begin{code}
(^)      :: a -> (a -> b) -> b
(*)      :: (a -> b) -> (b -> c) -> a -> c
(+)      :: (a -> b -> c) -> (a -> c -> d) -> a -> b -> d
(<>)     :: a -> b -> b
\end{code}


% The definitions above generate an equivalence relation between: the least one
% extending them, congruent to all operators.  
Equations can be proved by
substituting equals for equals.
One can also allow instances of the following ``$\zeta$'' Rule in proving equations.
\begin{center}
    \begin{tabular}{c} |x ^ a = x ^ b|  $\mbox{}\ruleimplies\mbox{}$ |a = b| \end{tabular}
\end{center}
with the side condition that |x| is fresh to both |a| and |b|.  This is
%an expression of `exponentiality':
%two values that behave the same as exponents of the same generic base are the very same value.
%I shall call this relation $\zeta$-equality.
%$\zeta$
is really a cancellation law.
All equations 
asserted below should be interpreted as $\zeta$-equations.

By using ``AMEN'' notation for the combinators addition, multiplication,
exponentiation and naught (aliases: nil, null, nihil, none, non-entity, nothing, nought, ought'nt \ldots),
we utter, in reverse, from nothingness to abundance, the last word
in combinators~\footnote{Thanks to Jim Laird for the joke. It is also the first word in the reversal of any prayer.}. 
\begin{spec}
    N  a b    = b 
    E  a b    = b a
    M  a b c  = E (E c a) b
    A  a b c  = M (E c a) (E c b)
\end{spec} 

 
\section{The BWICK combinators: |const|,|id|,$(\DOT)$,|flip|, diagonalisation}
\label{sec:cc}
 
A set of combinators and equational laws is combinatorially complete
if they suffice to simulate or compile $\lambda-$abstraction with $\beta$-contraction into
combinatorial code. 
For precise definition and full discussion, see \cite{Barendregt84} or
\cite{HindleySeldin86}.
 
It happens that |(+),(*),(^)| and |(<>)| are
combinatorially complete.  The gist of it is that you can translate, or
compile an expression $e$ written using a fresh variable $x$ 
into an applicative expression $[x]e$ in which that
$x$ does not occur, but only the combinators |(+),(*),(^)| and |(<>)|,
such that for arbitrary $a$, $([x]e)\,a = e[x\leftarrow a]$.
All occurrences of $x$ have been concentrated in a single argument place.

\iffalse
-- I doubt this would
-- be a sensible approach for implementing a functional language, though
-- the arithmetical combinators are among several sets of combinators,
-- complete or not, which it may be worth treating specially when
-- compiling or evaluating $\lambda$-calculus expressions.
\fi

We will see it more directly in section \ref{topic:Bohm-log}, by a remarkable
argument due to B{\"o}hm, but a simple way
to establish completeness it is enough to define the
following `BWICK' combinators in terms of them.  This particular set is well-known
and probably originally designed to be combinatorially complete.
All but one (|W|) are well known to Haskell programmers,
under the names in the left hand column of the following table.
The second column gives a possible definition as a
$\lambda$-term. The third column has the upper case capital letters given as names 
by Curry or some other authority.  The last column contains an aide memoire.
\begin{center}
\begin{tabular}[t]{lllcl}
  |flip  |&| (\f a b  |&| ->  f b a)    |&|   C |&|         -- swap the arguments of a binary function | \\
  $(.)$   &| (\f a b  |&| ->  f (a b))  |&|   B |&|         -- compose two functions                   | \\
  |id    |&| (\f      |&| ->  f)        |&|   I |&|         -- identity                                | \\
  |const |&| (\f _    |&| ->  f)        |&|   K |&|         -- return a function with a single value   | \\
          &| (\f a    |&| ->  f a a)    |&|   W |&|         -- this might be called diag, or dupl      |
\end{tabular}
\end{center}
For pronouncability, these are the BWICK combinators.

For comparision, here is a similar table for the arithmetical (AMEN) combinators
\begin{center}
\begin{tabular}{lllcl}
  |      |&| (\ m n s z  |&| -> n s (m s z))    |&|   A |&|         -- M (m s) (n s) | \\
  | flip | $(.)$  &| (\ m n s  |&| ->  n (m s))   |&|   M |&|         -- `natural' composition                   | \\
  | flip ($)    |&| (\ m n    |&| ->  n m)       |&|   E |&|         -- `natural' application                                 | \\
  | flip const |&| (\ _ n    |&| ->  n)        |&|   N |&|         -- dispose of an argument   | \\
\end{tabular}
\end{center}
Unfortunately, there seems to no pithy Haskell slang for
addition with arbitrary summands. Some sums have a short form though, 
such as | E + E = flip diag | .

The BWICK combinators are well known (and were perhaps even designed) to be
combinatorially complete.  (They were introduced in Curry's
thesis \cite{Curry30}. With tweaks for efficiency, David Turner used them to implement
his seminal function language SASL as described in \cite{DBLP:journals/spe/Turner79}. 
These combinators can be viewed as a refinement of the standard `SKI' combinators,
providing for important special \emph{linear} cases of |S| by using |B| and |C|.
A definition of |S| in terms of the arithmetic combinators is not difficult, but
there are better and worse ways to explain the idea.  A definition that isn't 
blindingly enlightening, is given as a footnote\footnote{One possible definition of $S$:
\[
        (\times) \times (\times)^{(\times)} \times (\times) \times ((\wedge) \times ((\wedge) + (\wedge))^{(\times)})^{(\wedge)}
\]
}, however it is more enlightening to first define $S$ as a binary operator. See section \vref{sec:log}. 

The definitions of the Curry combinators in terms of the
arithmetic combinators are quite simple, though it may not
be immediately clear where they come from.
\begin{code}
combC = (*) * (^) ^ (*)             -- called |flip| by fp'ers
combB = (^) * (*) ^ (*)             -- |(*) ^ combC| i.e. composition (.)
combI = evil ^ (<>)                 -- or |(<>) ^ (<>)|, |(^) * (^) ^ (*)|, inter alia
combK = (^) * (<>) ^ (*)            -- |(<>) ^ combC|
combW = (^) * ((^) + (^)) ^ (*)     -- |((^) + (^)) ^ combC|
evil  = error "Unthinkable"         -- not to be inspected
\end{code}
We finish this section by deriving these definitions from
the definition of each Curry combinator.


\def\commentbegin{\quad\{\ }
\def\commentend{\}}
The key thing is to start with the |C| combinator.
The main tool is the $\zeta$-law.
\begin{description}
\item[C] takes a binary function, and transposes or `flips' its
arguments.  
\begin{spec}

      C a b c  =  a c b        {- by def of |C| -}
               =  b ^ c ^ a    {- re-express using exponentiation -}
               =  (c ^ a) ^ b ^ (^)       {- by def of |(^)| -}
               =  c ^ (a * (b ^ (^)))     {- by def of |(*)| -}


\end{spec}

So, % by $\zeta$,

\begin{spec}

      C a b   =  a * (b ^ (^))          {- by $\zeta$ -}
              =  (b ^ (^)) ^ a ^ (*)    {- by def of |(*)| -}
              =  b ^ ((^) * a ^ (*))    {- def of |(*)| -}
\end{spec}

So, % by $\zeta$,

\begin{spec}
      C a    =   (^) * a ^ (*)          {- by $\zeta$  -}
             =   (a ^ (*)) ^ (^) ^ (*)  {- by def of |(*)| -}
             =   a ^ ((*) * (^) ^ (*))  {- by def of |(*)| -}

    
\end{spec}

So, % by $\zeta$, 
| C = (*) * (^) ^ (*) |, or to use exponential notation: $(\times) \times (\wedge)^{(\times)}$, or to use 
ordinary applicative notation with the |AMEN| combinators: |M M (M E)|.

The gruesome bit is now over. Most other combinators are plain sailing.

\item[B]
% As for |B|, it is clear that it 
is the transpose of |(*)|,
\ie{} $ (\times) ^ C $.  From the middle step in the
derivation of |C|'s arithmetic form, we therefore have as
a by-product

\begin{spec}
    B = (^) * (*) ^ (*)       {- alt. $(\wedge) \times (\times)^{(\times)}$ or |M E (M M)| -}
\end{spec}

\item[K]
% As for |K|, it is clear that it 
is the transpose of |(<>)|,
\ie{} $(\ZERO) ^ C$.  Therefore, just as for |B|,
\begin{spec}
    K = (^) * (<>) ^ (*)      {- alt. $(\wedge) \times (\ZERO)^{(\times)}$  or |M E (M N)| -}
\end{spec}

\item[I]
% As for |I|, it 
is the transpose of |(^)|, \ie{} $(\wedge)^C$. 
So we could take the following.
\begin{spec}
    I = (^) * (^) ^ (*)       {- alt $(\wedge) \times (\wedge)^{(\times)}$ or |M E (M E)| -}
\end{spec}

But we can also take any of the following:
\begin{spec}
    I = C * C
    I = evil^(<>)
\end{spec}
To explain $evil$, it is anything. Its value does not matter, and never needs to be inspected. But it exists.
\item[W]
%As for |W|, first l
Let's first express its transpose |CW|, which is quite easy. 

\begin{spec}
    CW a b   =  b a a        {- by def of |W| -}
             =  a ^ a ^ b    {- re-express -}
             =  (b ^ a ^ (^)) ^ a ^ (^)   {- by def of |(^)|, twice -}
             =  b ^ a ^ ((^) + (^))       {- def of |(+)| -}

\end{spec}

So by the $\zeta$-rule (twice) |CW = (^) + (^)|, that is $W = ((\wedge) + (\wedge)) ^ C$.
Note how this fits with the definitions of K and I.
\[ \begin{array}[t]{lll}
    K  &=  &(\ZERO)^C    \\
    I  &=  &(\wedge)^C    \\
    W  &=  &((\wedge)+(\wedge))^C ; ...
\end{array}
\]
\end{description}
This completes the derivation of the |BWICK| combinators. 

\iffalse
Amusingly, 
\begin{spec}
 1   = (^)^C            {- |(^)| and |1| mutually converse -}
 1   = C^2              {- |C| is a square root of unity -}
 1^W = (^)^W            {- self application -}
 W   = C*W              {- |W| is symmetric in first arg -}
 W   = (1^C + 1^C)^C    {- ie. |W| is a conjugate of 2 -}

 K = (<>)^C             {- |K| and |(<>)| mutually converse. -}
 1 = (<>)^(<>) = ((^)*) ^ ((^)*) 
 1^W ((^)*) = 1^W (<>)
\end{spec}
Amusements like these abound in the AMEN arcade, in
Many a familiar
combinator has an eerie arithmetical doppelg{\"a}nger. 
\begin{spec}
 W   = (1^C + 1^C)^C    {- ie. |W| is a conjugate of 2 -}
 K = (<>)^C             {- |K| and |(<>)| are each other's. -}
\end{spec}
%Appendix  \ref{sec:arcade} contains a selection. 
\fi

\section{\label{sec:examples}Further examples: pairing, |S|, and fixedpoints.}

\subsection{\label{sec:pairing}The pairing combinator $(\COMMA)$ and currying.}


Consider first pairing as a binary operator: | (a,b)|.
In fact, the Church encoding of pairs gives | (a , b) = (a ^ (^)) * (b ^ (^)) |, with the first and second
projections of |p| being given by  | (K ^ (^)) | and | (0 ^ (^)) | respectively.

One can shuffle the parameters around to obtain a purely arithmetical
(and linear)
expression for the pairing combinator $ (\COMMA) = (\wedge) \times (\times) \times
(\wedge)^{(\times)}$. 

Hand in hand with pairing (and indeed exponentiation) comes currying:
| curry f x y = f (x,y) |.
We can immediately see that | curry (a ^) = a |, so that
$(\wedge) \times$ | curry | $=1$.
\ie{} |curry|
is a multiplicative inverse of the exponentiation combinator. Among
its other strange properties, | id ^ curry | is the pairing combinator
$(\COMMA)$. 

Two possible expressions for the combinator | curry | are 
$ B \times (,)^{(\times)}$ (which is linear) and $K \times (,)^{(+)}$
(which is non-linear, since it involves both addition and zero).
These can be made purely arithmetic by translating $B$, $K$ and $(\COMMA)$ into arithmetic.

\subsection{\label{sec:Scomb}The combinator |S|, with |S a b c = a c (b c)|.}
Consider |S| first as a binary combinator, written infix with $\circ$
as in $a \circ b$.  Its defining equation is 
$(a \circ b) x = a\, x\, (b\, x)$.
As a matter of fact $a \circ b$ can be expressed as 
$b ^{(\COMMA)} + a ^{(\wedge)}$.

In notation without superscripts, one of many possible definitions of
|S| is this horrible specimen:
\begin{spec}
  (*) * ((*) ^ (*)) * (*) * ((^) * ((^) + (^)) ^ (*)) ^ (^)
\end{spec}
Using superscript notation, it is possibly even more alarming. 
\[
\begin{array}{l}
%  (\times) \times (\times) ^ {(\times)} \times (\times) \times {((\wedge) \times ((\wedge) + (\wedge)) ^ {(\times)})} ^ {(\wedge)}
 (\times) ^ {1 + (\times) + 1} \times {((\wedge) \times ((\wedge) + (\wedge)) ^ {(\times)})} ^ {(\wedge)}
\end{array}
\]

A straightforward way to define |S|, is first to define a linear
version, |S' a b c c' = a c (b c')|.
For example, $S'\, a\, b = a \times b ^ {(\times)}$,
so $S' = (\times)^{1 + (\times)}$). 
Finally, define |S| from |S'| by
diagonalisation: $S\, a\, b = (S'\, a\, b)^W$ or $S = S' \times W^B$.
The matter of fact mentioned above arises from more arithmetical considerations, 
and will be explained in section \vref{sec:log} on logarithms.

%The reader may wish to know
\subsection{\label{sec:fp}Curry and Turing fixed-point combinators.}
Among endless variations, two fixed-point combinators of historical significance are
Curry's (\cite[p. 178]{CurryFeys}) and Turing's
\cite{DBLP:journals/jsyml/Turing37a}.
Both their fixed point combinators use self application.
This of course banishes us from the realm of combinators that Haskell can type,
but what the heck.
%
We call the self application combinator |sap|.
\begin{spec}
      sap x = x x = W (^) x = W 1 x 
  So  sap = (^)^W = 1^W
\end{spec}
%Note that the expressions |(^)^W| and |1^W| do not typecheck.

We call Curry's combinator simply $Y$.
\begin{spec}
    f^Y  = sap (sap * f)
      Y  = (sap *) * sap 
         = sap ^ ((*) + 1)
\end{spec}
$Y$ can thus be seen as applying
the successor of multiplication 
to the value |sap|.

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

%\newpage
\section{Algebra}
\label{sec:algebra}

In the presence of the $\zeta$-rule, 
\begin{enumerate}
  \item |(+,(<>))| forms a monoid.

  \item |(*,1)| forms a monoid, where |1 = combI| .

  \item pre-multiplication |(a *)| distributes over the additive monoid:  |a * (b + c) = a * b + a * c| and |a * (<>) = (<>)| .

  \item exponentiation |(a ^)| maps the additive monoid to the
    multiplicative monoid:  |a ^ (b + c) = a ^ b * a ^ c| and |a *
    (<>) = (<>)| .
    This was Napier's idea: to avoid the `slippery' errors that can
    arise in the multiplicative world by expeditiously working instead
    on more solid ground, in the additive monoid.
    \footnote{ Napier famously wrote in the preface to his ``Mirifici logarithmorum canonis descriptio'' (1614): \begin{quotation}
Since nothing is more tedious, fellow 
mathematicians, in the practice of the 
mathematical arts, than the great delays
 suffered in the tedium of lengthy 
multiplications and divisions, the finding of 
ratios, and in the extraction of square and 
cube roots– and in which not only is there the time delay to be considered, but also the 
annoyance of the many slippery errors that can arise: I had therefore been turning 
over in my mind, by what sure and expeditious art, I might be able to improve upon 
these said difficulties.
% \ldots there is nothing \ldots so troublesome to mathematical practice \ldots than the
% multiplications, divisions, square and cubical extractions of great numbers, which
% besides the tedious expense of time are for the most part subject to many slippery errors,
% I began therefore to consider … by what certain and ready art I might remove those hindrances.
    \end{quotation}
He wanted to move between the `slippery' multiplicative world of geometric progressions and the `expeditious' additive world of arithmetic progressions;
to multiply, divide and take roots by adding, subtracting and dividing.
}

  \item exponentiation |(a ^)| maps the multiplicative monoid to the
    composition monoid $(\cdot,\id)$ of unary functions over our
    arithmetical domain:  |a ^ (b * c) = (a ^ b) ^ c| and |a ^ 1 = a|,
    \ie{} |^(b * c) =  (^c)| $\cdot$ |(^b)| and |(^1) = id |.
\end{enumerate}

Addition and multiplication are not in general commutative, there need be no subtraction (or division),
and post-multiplication need not distribute over sums.
I have heard such structures called 
a `near-semiring' (with unit). As rings go, this is a bit enfeebled.
However, rings do not generally have exponentiation, which makes up
for the feeble structure on $+$ and $\times$.
Personally, I call the algebraic structure (even without the ``funny''
numbers |(^),(*),(+)|, but only $0$ and $1 = 0^0 = $ | id | as constants ) an `elementary arithmetic',
or the algebra of elementary arithmetic. 

The laws of | (+),(<>),(*),1,0,(^)| above 
are within a gnat's whisker of the basic laws of 
ordinal arithmetic with (with simple non-commutative addition and multiplication). 
However the coincidence is not exact.  In an ordered world, when $a$ is
``numerical'', which is to say a ``true'' number,
the following laws obtain.
\begin{spec}
   1 ^ a = 1
   (<>) * a = (<>)
\end{spec}
Matters are different when $a$ is an arbitrary combinatory expression.
For example, when $a = K$, $1^K$ is the constant function whose value is the
identity.
To find counterexamples to equations, our basic tool is
the assumption that no constant
function equals the identity function, or equivalently $0 \not= 1$. 
From this other distinctions follow: $0 \not= K$, $1 \not= K$, $2
\not= K$, \etc.
To distinguish $1^a$ from $1$, clearly, $a$ must not be numerical, but
something weird. We can choose $a = K$, since $1^K$
is $\zeta$-equivalent to $0$,
which is distinct from $1$. 
A counterexample to the second is a little more circuitous. 
%o find an $a$ with $(0 \times a) \not= 0$, we can try to distinguish
%them at some argument $x$. So we look for $a$ such that $1 ^ a$ is
%distinct from $1$. 
Again, $a$ must be something non-numerical. 
Let us try exponentiation itself: $(\wedge)$. 
Applying both sides to successive variables $x$ then $y$, the left
hand side becomes $1 ^ y$, and the righthand side becomes $y$. So
if $y$ is $K$, the lhs is $0$ and the right is $K$. But $0 \not= K$,
since
if $0 = K$ then $1 = 1^0 = 1^K = 0$. So exponentiation is one
counterexample to the second law.
\iffalse
$1^K$ happens to be $(\ZERO) \times 1^{(\wedge)}$,
so $1^{\wedge}$ is a counterexample for the second
\begin{spec}
   1 ^ K =  (<>) * (1 ^ (^))           -- $\not=$ the identity 1
   x ^ ((<>) * K) = (<>) * (1 ^ (^))   -- whereas | x ^ (<>) = 1 | 
\end{spec}
\fi

An intriguing feature of this arithmetical world is that
interesting laws (particularly for logarithms) sometimes hold with greater generality than one might
expect.~\footnote{For example $\log_x (\alpha ^ b) = (\log_x \alpha) \times b $, merely in case $b$ does not contain $x$. It need not be numerical. }
%.  This is because we don't have |1 ^ a = 1|: for example |1 ^ K = (<>)|. 
Life is not always so serious though, and we can simply enjoy the
sheer weirdness of things.  For example, call functions $f$ and $g$
converse if $f = g^C$. Converse functions share the same diagonal. It follows immediately that $C$ is not
its own converse, \ie{} not commutative. 
However, it is a square-root of identity distinct from identity. Maybe
we could consider Gaussian `numbers', that have 
with an imaginary part with $C$ as a factor.

%Compared to a ring, we don't have 
%additive inverses, addition need not be commutative, and 
%multiplication distributes over addition work only one way round.
%Of course the signature of a ring doesn't have exponentiation. 



\paragraph{Axioms as closed equations}
As an exercise in pointlessness, one can express the axioms of this structure
the monoid laws, the distribution laws and so on,
in the form of equations between closed expressions, albeit gigantic and inscrutable.
The result is not particularly enlightening, but it calls to mind
Curry's finite axiomatisation of the closed consequences of the $\zeta$-rule. 
\iffalse
What consequences of the $\zeta$-rule, do \emph{not} follow from these equations?
%More on this anon.


The unit laws for the monoids:
%\begin{spec}
% 1 = (+) * ((<>)^)  = ((<>)+)  
% 1 = (*) * (1^)     = (1*) 
%\end{spec}
\[
\begin{array}{lll}
 1 &= (+) \times (\ZERO)^{(\wedge)}  &= (\ZERO)^{(+)}   \\
 1 &= (\times) \times 1^{(\wedge)}     &= 1^{(\times)}
\end{array}
\]

%\begin{spec}
% 1 = (+) * ((<>)^)  = (+)^C * ((<>)^)  
% 1 = (*) * (1^)     = (*)^C * (1^)     
%\end{spec}
% In some respects |C| seems to behave like |-1|.  This would make a square root of |C|
% something like the complex number $i$.  This in turn would make a solution for $x$ of |(^)^ (i * x) = 1| a
% candidate for $\pi$.  I know of no square root for |C|, but I can express it in the form |R ^ R ^ R|.
%
The associativity laws of the monoids can be put in the form of commutativity laws.
%\begin{spec}
% (c ^ (*)^C ) * (a ^ (*)) = (a ^ (*)) * (c ^ (*)^C)
% (c ^ (+)^C ) * (a ^ (*)) = (a ^ (*)) * (c ^ (+)^C)
%\end{spec}
\[ \begin{array}{l}
 (c \wedge {(\times)}^C ) \times (a ^ {(\times)}) = (a ^ {(\times)}) \times (c \wedge {(\times)}^C) \\
 (c \wedge {(+)}^C ) \times (a ^ {(\times)}) = (a ^ {(\times)}) \times (c \wedge {{(+)}^C})
\end{array}
\] 
% (((*)^C) gamma)*((*) alpha) = ((*) alpha)*(((*)^C) gamma)
% (((+)^C gamma))*((+) alpha) = ((+) alpha)*(((+)^C) gamma)
%
These can then be reduced further to equations between constants.
%\begin{spec}
% ((*) ^ C) * (*) * ((*)*)    = ((*) ^ C) * ((*) ^ C) * ((*) ^ (*))
% ((+) ^ C) * (*) * ((+)*)    = ((+) ^ C) * ((*) ^ C) * ((+) ^ (*))
%\end{spec}
\[ \begin{array}{ll}
 (\times) ^ C \times (\times) \times {(\times)}^{(\times)}    &= (\times) ^ C \times (\times) ^ C \times (\times) ^ {(\times)} \\
 (+) ^ C      \times (\times) \times (+)^{(\times)}               &              = (+) ^ C \times (\times) ^ C \times (+) ^ {(\times)}
\end{array} \] 
%

The simpler of the 
two distributivity laws amounts to
%\begin{spec}
%   1 + 0 ^ K     =  0 ^ K
%\end{spec}
\[\begin{array}{ll}
   1 + (\ZERO) ^ K     &=  (\ZERO) ^ K
\end{array}\]
%\begin{spec}
%   0 ^ (*)     =  0^(1 + (^))
%\end{spec}
As it happens, for any |a|,  $a + (\ZERO) ^ K = (\ZERO) ^ K$ .

As for the more complicated (and non-linear) distributivity law, after some labour, I found (and checked) that:
%\begin{spec}
%  (*) * ((*) ^ C) * ((+) ^ (*))   = (*) + (*) ^ K + (*) ^ 2          STOP
%\end{spec}
\[
  (\times) \times (\times) ^ C \times (+) ^ {(\times)}   = (\times) + (\times) ^ K + (\times) ^ 2  \;.
\] 
%the right hand side of which is amusingly quadratic in |(*)|.
\iffalse
The other one is too fiddly for me to work out reliably~\footnote{I got as far as this:
\[ ((\wedge) + (\wedge)) 
\times 
( ((\times) \times b ^ {(\wedge)}) \times (+) \times ((\times) \times c ^ {(\wedge)}) ^ {(\times)}
) ^ {(\wedge)}  
= (\times) \times (b + c) ^ {(\times)}
\]
}.
\fi
%At any rate, it is an equation between two mind-boggling constants. 

%and if not to know what's missing. 
%It looks as if it will be mere arithmetical eye-disease. 
\fi



\paragraph{Exponentiality} 
The rule of exponentiality $\zeta$ says that if things $t$ are the same as
exponentials $x^t$ where the base $x$ is a fresh variable, then they're just the same.
Everything is a function, and no more than a function.  It is entirely indispensible.
%We've seen many consequences.

A remarkable discovery of Curry's was that finitely many instances of $\zeta$
suffice to axiomatise all consequences of
$\zeta$.  A combinatory algebra that satisfies Curry's equations is
(I think, perhaps wrongly) known as an extensional combinatory
algebra.
Quibbles can arise about whether the term `extensional' is
appropriate, as what is meant is schematic equality as
legitimated by the $\zeta$-rule, but whether or not the terminology is appropriate,
it is in widespread use.
One can read about these algebraic axioms in Hindley and Seldin's book
\cite[Ch. 8]{HindleySeldin86}, and about more full-blooded, genuine
or semantical, forms of extensionality in Selinger's paper, \cite{Sel2002-combinatory}. 

Curry's equations \label{rmk:Curry-zeta}
were written (TODO: check) using the $S$ and $K$ combinators,
but they can be written using any combinatorially complete set.
A key r{\^o}le is played by the |K| and |S| combinators, the former
being used to throw away an unwanted argument, and the latter to
feed arguments to both parts of an expression of exponential form.
(Expressions of the form $t^K$ are in facts closed under addition,
and indeed multiplication by arbitrary factors, as we shall see shortly.)

In an arithmetical setting, these equations between closed terms can be obtained
by `pointlessly' removing variables from the following laws. (I allow myself to go a
bit rough-shod across some fearsome-subtle shenanigans.)
\renewcommand{\circ}{\mathbin{{{}_{{}^\rhd}}}}
\newcommand{\cric}{\mathbin{{{}_{{}^\lhd}}}}
\[ 
\begin{array}{llrr}
  (\wedge)^K \circ x \circ y         &  = y \circ x  \\
  (\times)^K \circ x \circ y \circ w &  = y \circ (x \circ w)  \\
  (+)^K \circ x \circ y \circ w \circ z &  = y \circ w \circ (x \circ w \circ z) \\
  (\ZERO)^K \circ x \circ y & = y  \\
  (x \wedge y)^K                      & = x^K \cric y^K && \mbox{homomorphism}\\
  x^K \circ 1                  & = x             && \mbox{universality}
\end{array}
\]
Here $\circ$ is used as an infix form of the $S$ combinator \label{rmk:doppel}; $\cric$ is an infix form of
the converse of $\circ$; and ${}^K$ \label{rmk:constant} is a superscript form of the 
$K$ combinator.  These have quite pithy arithmetical expressions, given 
in section \ref{sec:log}.

Note that beside $(x \wedge y)^K = x^K \cric y^K$, we also have the laws $(x \times y)^K = x^K + y^K$, and $ 1^K = (\ZERO)$.
So a lot of structure is mapped around by ${}^K$. What is important is that the defining equations for the
combinators are preserved.

\iffalse
For the time being, I record here Curry's axioms in $SK$ form.  
Define $x \circ y$ to be |S x y|, or more arithmetically 
\begin{spec}
   y * (,) + x * (^) 
\end{spec}
We might think of $(\circ)$ as pointwise lifted application,
and its flip as pointwise lifted exponentiation.  
The axioms can then be written as follows. 
Of course they can be $\zeta$-reduced further to equations between constants.
\[
\begin{array}{llrr}
  S^K  \circ x \circ y \circ z & = x \circ z \circ (y \circ z)  \\
  K^K  \circ x \circ y         & = x \\ 
  (x y)^K                      & = x^K \circ y^K && \mbox{homomorphism}\\
  x^K \circ 1                  & = x             && \mbox{universality}
\end{array}
\]

I think it is clear what is going on with the definitions of the
combinators, and how they (and the remaining laws) should be arithmetised.
One obviously wants
\[ 
\begin{array}{ll}
  (\wedge)^K \circ x \circ y         &  = y \circ x  \\
  (\times)^K \circ x \circ y \circ w &  = y \circ (x \circ w)  \\
  (+)^K \circ x \circ y \circ w \circ z &  = y \circ w \circ (x \circ w \circ z) \\
  (\ZERO)^K \circ x \circ y & = y 
\end{array}
\]

\fi

As for the `universality' equation, it is still a bit mysterious to me, but it seems to
say that the ${}^K$ homomorphism has some uniqueness property.   Note: |1| is not in the image of ${}^K$.
\footnote{
  Curry's equations remind me slightly of the axioms for
  Haskell's applicative functors, if only notationally. 
  With applicative functors (discovered by Conor McBride, among others), it seems that
  one cares about the linear combinators only, namely $B$, $I$ and $(\$)$.
  (One could use $(\wedge)$,$(\times)$.) There
  is no place, one would guess, for $S$, $K$ or $W$ among the laws for applicative functors.
.
  A more striking difference is that where Curry has the law  $ (x^K) \circ 1 = x$, Conor has an
  interchange law (translating it into our more comely notation)
  $(y \wedge)^K \circ x = x \circ y^K$. This happens to be true; but more is true.
  In fact, 
  $(\wedge)^K \circ x \circ y = y \circ x$ is one of the axioms for the linear combinators.
%  $z^K$.
  For an applicative functor one needs this only when $x$ 
  has the form ${\_}^K$. 
}

TODO: Freyd \cite{Freyd89}; Selinger \cite{Sel2002-combinatory}; Statman \cite{Statman14}.

\paragraph{Ideals, more or less.}

A paper by B{\"o}hm (\cite{bohm:1982}) is particularly concerned with
the ring-like structure described above. 
%\ref{sec:algebra}.
In it, B{\"o}hm introduces a notion that is clearly inspired by the notion of 
an ideal in a ring, 
A class is called by B{\"o}hm a ``notion of zero'' if it contains |(<>)|, is closed
under addition, and for arbitrary |a| is closed under both |(a *)| and |(* a)|.

One example: $Z =$ the class of terms that can be put in the form $a^K$, or equivalently $(\ZERO) \times (a\wedge)$  -- these represent constant functions,
\label{rmk:constant}
that as powers of any base have the same value. All `constants' are $\zeta$-equivalent to terms of the form $a^K$.~\footnote{They play a major r{\^o}le
in Curry's investigation of the $\zeta$-law at section \ref{rmk:Curry-zeta}.}  The following are
straightforward to prove with the $\zeta$-rule.
%consequences of extensionality. 
%(One can alternatively describe these |(<>)*(a^)|.)
\begin{itemize}
\setlength{\itemsep}{0pt}
\setlength{\topsep}{0pt}
\setlength{\parskip}{0pt}

\item Closure under addition:
%  \begin{spec}
%            (\ZERO) = 1^K
%       a^K + b^K = (a * b)^K  
%  \end{spec}
  \[\begin{array}{ll}
            (\ZERO) &= 1^K   \\
       a^K + b^K &= (a \times b)^K
   \end{array}  
  \] 

\item Closure under scaling by arbitrary factors on left and right:
%  \begin{spec}
%      b * (a^K) = a^K
%      (a^K) * b = (a^b)^K
%  \end{spec}
  \[\begin{array}{ll} 
      b \times (a^K) = a^K  \\
      (a^K) \times b = (a \wedge b)^K
  \end{array}\]
  Because of the last scaling law, the class $a^K = (\ZERO) \times (a \wedge)$ already includes the
  class $(\ZERO) \times (a_1 \wedge) \times \cdots \times (a_k \wedge)$.

\end{itemize}

What does one do with an ideal?  Quotienting.  So one considers $a$
and $b$ to be `equal' if $a$ and $b$
differ only by an element of the ideal (\ie{} by `zero'), that is by addition of a 
`constant', \ie{} $a = b + c^K$.  Equivalently, $a = b \times c^B$, which seems to mean that $a$ and $b$ are the same up to scaling
by a `constant' factor.
%It might be interesting to investigate such constructions.

Perhaps in pursuit of duality, B{\"o}hm introduces also the term ``notion of infinity'' for a set
of  terms closed 
under |(a+)| and |(+a)| for any |a|.  One example is the set $I$ of terms of the form
$a\times K$.  
\begin{itemize}
\setlength{\itemsep}{0pt}
\setlength{\topsep}{0pt}
\setlength{\parskip}{0pt}

\item Closure under arbitrary addition on left and right:
%  \begin{spec}
%      b * (a^K) = a^K
%      (a^K) * b = (a^b)^K
%  \end{spec}
  \[\begin{array}{ll} 
      b + (a \times K) = a \times K  \\
      (a\times K) + b =
%      (a \times (,) + b \times (\wedge))
      (a\cric b)
      \times K
  \end{array}\]
(Here $\cric$ is infix notation for the converse of the binary 'S' combinator, that was
introduced in connection the Curry equations. 

\end{itemize}
Sheer duality might lead one to conjecture that this particular `notion of infinity' $a \times K$ might be
closed under multiplication. It isn't, nor, to be frank is this form of expression of much obvious interest.
It might be that some other forms of expression (\eg{} $a + K$, $a ^ B$,
|(a^)| $=a^{(\wedge)}$, \dots) have interesting closure properties with respect to addition, scalar multiplication, and so on.

B{\"o}hm's paper teems with monoidal and cartesian structures: the 
monoid of lists under concatenation, the monoid |(*,1)|
of endofunctions on a set under composition, the monoid |(+,0)| of endofunctions of endofunctions
under pointwise-lifted composition, products, pairs and their projections.
%Among much other highly interesting apparatus, B{\"o}hm
%points out (Church-encoded) ordered pairs (as in Lisp), their projections, and currying.
In the next section, we make use of his apparatus to extend Napier's laws of logarithms.


\section{Logarithms}
\label{sec:log}

One can daydream of using $\lambda$ogarithmic notation for lambda-abstraction, with
|a ^ (log_x e) = e[x<-a]|.  Here the `base' is a bound variable, but no matter:
one obtains Napier's laws of logarithms.\footnote{It has to be said: but not the laws that deal with change of base.}
For example, whether or not the base occurs in 
both factors of a product, the product is turned into a sum.  If
$a$, $b$ and $c$ are expressions such that $c$ contains no occurrences of $x$, then
we have the following equations, once familiar to schoolchildren.
\begin{spec}
                log_x (a * b)  = (log_x a) + (log_x b)
                log_x 1        = (<>)
                log_x (a ^ c)  = (log_x a) * c
                log_x x        = 1
\end{spec}
The last equation is not difficult to remember, and the others can be summed up
in the following formula for the logarithm of a product of constant powers.
\begin{spec}
     log_x (b1 ^ c1 * ... * bn ^ cn) 
     = (log_x b1) * c1 + ... + (log_x bn) * cn
\end{spec}
It should be stressed that this equation holds regardless of whether
the coefficients |c| are numerical.

Now let us consider `linear' logarithms, where we care about how many times 
the `base' |x| occurs in |e|.  These obey many delightful arithmetico-combinatorial
laws, that can be figured out on the edge of a newspaper.
% when stranded on a broken train,
% or on the average paper napkin.  
The following are easily verified, where $a, b, b_1, \ldots b_k$ are
expressions that do not contain any occurrences of the variable $x$.
\begin{spec}
 log_x x                   = 1
 log_x (a x b)             = log_x (b ^ x ^ a)
                           = log_x ((x ^ a) ^ (b^)) 
                           = a * (b^) 
 log_x (a x b1 .. bk)      = a * (b1 ^) * .. * (bk ^) 
 log_x (a x x)             = ((^)+(^))*(a ^)
 log_x a                   = (<>) * (a ^)  =  a ^ K
\end{spec}

In fact, any linear abstraction~\footnote{ie, in which the bound variable occurs exactly once,
so not like the left hand terms in the last two equations.} 
is a product (ie. a composite) of factors
that each look like
\begin{spec}
                  a * (b1^) * ... * (bn^)                     STOP
\end{spec}
In other words, the following is a normal form for logarithms to a linear base.
\[            \prod_{i : [1,m]} (a_i \times \prod_{j : [1,n_i]} b_{ij}^{(\wedge) })
\]
%The logarithm of such a term (to any base) is
%\[            \sum_{i : [1,m]} (a_i + \sum_{j : [1,n_i]} b_{ij}\times{(\wedge) })
%\]
The logarithm of the last expression to a fresh (not necessarily linear) base $y$ is then easily attained:
\[            \sum_{i : [1,m]} (\log_y a_i + \sum_{j : [1,n_i]} \log_y(b_{ij})\times{(\wedge) })\;.
\]


Naperian logarithms deal with non-linear abstraction, but we only know
how to deal with multiplicative structure and constant powers. Can we take logarithms
of terms of general exponential form, where the `base' occurs in both the exponent and the iterand?
What about logarithms of sums?
B{\"o}hm \cite{bohm:1979}\footnote{I am
very grateful to Roger Hindley for a copy of this almost unobtainable paper.}
showed how this works.
He was well aware of the formal similarity between $\lambda$-abstraction
and taking logarithms.
In fact, he devised an innovative form of bracket abstraction, by
extending the logarithm operation to arbitrary arithmetical expressions,
yet preserving its Naperian core.

\label{topic:Bohm-log}


To take the logarithm of a term of \emph{general
exponential form} (where the exponent need not be constant), we re-express
it as a product of constant powers.
%In essence, that is the same problem addressed by the S combinator, except
%that lifts application point-wise instead of lifting exponentiation base-wise.
The trick is to use Church's pairing combinator $(\COMMA)$  | = \ a b c -> c a b | \footnote{For example: $(\wedge) \times (\times) \times (\wedge)^{(\times)}$.
This we mentioned before in section \vref{sec:pairing}.}.
This satisfies
\[\begin{array}{l} %\begin{spec}
     (a , b) = a ^ {(\wedge)} \times b ^ {(\wedge)}
     \\ K \wedge (a , b ) = a
     \\ (\ZERO) \wedge (a , b ) = b
\end{array}\] %\end{spec}
Note that | (a ^ b) c = b ^  (a , c)|. So any exponential term |a ^ b| can be expressed as a product of constant powers.
\begin{spec}
     a ^ b = (\ c -> b ^ (a ,c) ) = (a ,) * (b ^) = (a ^ (,)) * (b ^ (^)) 
\end{spec}
%\[\begin{array}{llll}      b \wedge a =  c \mapsto ((a ^{(\wedge)}) \cdot (b^{(,)})) c) = b^ {(,)} \times a ^ {(\wedge)} \end{array}\]
Napier gave us the logarithms of such quantities.
Applying his technique, we alchemise the
(slippery) product monoid into an
(expeditious) sum monoid. 
We have thus an `exponential' doppelganger $S^C$ of the |S| combinator,
referred to previously as $\rhd$ in section \ref{rmk:doppel} in connection with Curry's
treatment of the $\zeta$-law. Using the infix notation of that section 
\[
      S^C\, a\, b \;=\; a \lhd b \; = \; a \times {(,)} + b \times {(\wedge) }
\]
This is what we need to extend logarithms to general exponential form,
where the exponent is not constant. 
\[\begin{array}{ll}
     \log_x (a \wedge b)  &= (\log_x a) \lhd (\log_x b)
\end{array}
\]
Fortunately, this agrees with the Naperian law when $b$ has no occurrence of $x$.

How about logarithms of \emph{additive form}? We already know how to do this by brute force,
since a sum can be expressed as an exponential to an exponential. Is there something more dainty?

The trick is 
currying.  Let |curry| be some closed expression such that |curry f x y = f (x,y)| \footnote{Two examples are 
$ B \times (\COMMA)^{(\times)}$ and $K \times (\COMMA)^{(+)}$. The second one
comes from expressing |curry f x| as $x^{(\COMMA)} \times x^{f^K}$,
then taking logarithms to the base $x$ to get |curry f = |$(\COMMA) + f^K$}. 
It is direct that | curry| $(a^{(\wedge)})  = a $, and so | curry|
$(a^{(\wedge)})\,x  = x^a $.
But much more obtains:
$$
\curry(a^{(\wedge)} + b^{(\wedge)}) x = x^a + x^b\;.
$$
(We even have |curry|$(a^{(\wedge)} \times b) x = x^a \times b$, regardless of whether $b$ is numerical.)
This gives B{\"o}hm's amazing formula for the logarithm of a sum:
%\begin{spec}
%     log_x (a + b)  =  curry ((log_x a)^)  + ((log_x b)^)
%\end{spec}
\[   \log_x (a + b) =  \curry ((\log_x a)^{(\wedge)}  + (\log_x b)^{(\wedge)})
\]

Finally, as you may perhaps guess from looking at the logarithm of a binary sum,
the logarithm of zero, to any base, is Curry'd naught, |(<>)^K|.  This
`eats' anything, in the sense that $a + (\ZERO)^K = (\ZERO)^K$.  
Curry'd one, on the other hand, is the pairing combinator $(\COMMA)$
%But for any term | a + 0^K | is $\zeta$-equivalent to |0^K|. Perhaps | 0^K| is $-\infty$?
For convenience, I've put the laws of B{\"o}hmian logarithms 
in a table in figure \vref{fig:logBohm}. % on page \pageref{fig:logBohm}.
\begin{figure}
  \centering
  \begin{tabular}[t]{lll}
  \multicolumn{2}{l}{pairing apparatus: 
  $(a , b) = a^{(\wedge)} \times b^{(\wedge)} $} & 
  ; $\curry\, f\, x\, y = f (x,y) $
  \\[2mm]
  $\log_x (\prod_i a_i)$ &= $ \sum_i (\log_x a_i)$ &
  ; $\log_x 1  = (\ZERO) $
  \\
  $\log_x (\sum_i a_i)$  &= $\curry (\sum_i (\log_x a_i)^{(\wedge)} )$ &
  ; $\log_x (\ZERO) = \curry (\ZERO) = (\ZERO)^K$
  \\
  $\log_x (a \wedge b)$ &= $(\log_x a) \times (,) + (\log_x b) \times (\wedge) $
  \\
  $\log_x (a \COMMA b)$ &= $(\log_x a) \times{ (\wedge)}+ (\log_x b) \times{ (\wedge)} $

  \end{tabular}
  \caption{Table of B{\"o}hm's $\lambda$ogarithms}
  \label{fig:logBohm}
\end{figure}

\iffalse
\paragraph{logarithms with numerical base.}
Our `logarithm' is with respect to `$x$', a cardboard cut-out of
a base.  How does it compare with the ordinary integer logarithm, with a base greater than 1?
I don't know.  What seems to be lacking is some way of defining when
one combinatory expression denotes something at least as `big' as another.

At least when $m > 1$, we  have a 
Galois~\footnote{
Nearby, there are other Galois connections in the non-negative integers. Writing $k \div m$ for the greatest
multiple of $m$ not exceeding $k$, for $m > 0$
\[ %\begin{spec}
\begin{array}{ccc}
           m\times n \leq k  &      \equiv  &    n \leq (k \div m)  \\
           (m \times)  &      \dashv  &   (\div m)\;.
\end{array}
\] % \end{spec}
Moreover, writing $k \dotdiv m$ for the greatest supplement of $m$ that does not exceed $k$,
when $m$ does not exceed $k$, we have
\[ %\begin{spec}
\begin{array}{ccc}
           m +  n \leq k  &      \equiv  &    n \leq (k \dotdiv m)  \\
           (m +)  &      \dashv  &   (\dotdiv m)\;.
\end{array}
\] % \end{spec}
}
connection 
\[ %\begin{spec}
\begin{array}{ccc}
           m^n \leq k  &      \equiv  &    n \leq log_m k    \\
           (m \wedge)  &      \dashv  &   log_m
\end{array}
\] % \end{spec}
However it is not at all clear what to take for the partial order $\leq$ (nor the strict order $<$) when our `numbers'
include such non-standard quantities as $(\wedge)$, $(\times)$ and $(+)$.

\paragraph{True numbers.}
One wants relations such as $\leq$ to coincide 
with the usual arithmetic relations on `true' numbers. The question is, what is a true number? 

An \emph{ordinal} number $n$ will satisfy things like $1^n = 1$, maybe $0\times n = 0$; a \emph{finite} number will also
make good the commutativity of $+$ and $\times$. Are `true' numbers non-negative? Non-fractional? Finite? Well-founded?
Are the rest only dangerous Saracen magic?

(Should one have a satisfactory definition of $\leq$, one would rather like that $\leq$ had various suprema,
such as $\cup \{ \,n\, : \, m^n \leq k\,\}$
(that would be the logarithm $log_m\,k$, $m>1$)),
or $\cup \{ \,n\, : \, m\times n \leq k\,\}$ (the division $k \div m$, $m>0$).
\fi

\iffalse
It is time we had a picture. See 
 figure \ref{fig:logbook}.
\begin{figure}
\begin{center}
%\includegraphics[scale=0.5]{Napier10.pdf}. 
\includegraphics[scale=0.75]{Napier10.pdf}. 
\end{center}
\caption{Front page of Laird Napier of Merchiston's (1614) book on logarithms.}
\label{fig:logbook}
\end{figure}
\fi

\iffalse
\section{Arithmetical calculus}

The arithmetical combinators are rather fascinating, but it is
easy to make mistakes when performing calculations.
We now write some code to explore on the computer
the evaluation of arithmetical expressions, built out
of our four combinators.

The first piece of code is an evaluator, that computes the normal form
of an expression (with respect to some rewriting rules) if one exists.
This lets us see the value of an expression, but not how it was
arrived at. The second piece of code is for watching the reduction
rules in action.

There are various systems and reduction strategies of interest.  They
arise from the algebraic structure: the additive and multiplicative
monoids, weak distributivity, etc.


Here is a datatype |E| for arithmetical expressions.  The symbols 
for the constructors are chosen to suggest their interpretation as
combinators.

\begin{code}
infixr 8  :^: 
infixr 7  :*:
infixr 6  :+:
\end{code}

\begin{code}
data E  = V String | E :^: E | E :*: E | E :+: E 
          deriving (Eq)    -- (Show,Eq)
\end{code}

We can think of these expressions as fancy Lisp S-expressions, with three
`cons' operations, each with an arithmetical flavour.  Like Neapolitan ice cream.  

It is convenient to have atomic constants identified by arbitrary strings.
The constants |"+"|, |"*"|, |"^"| and "|0|" are treated specially.
\begin{code}
(cA,cM,cE,c0,c1) = (V"+",V"*",V"^",V"0",V"1")
\end{code}

For each arithmetical operator, we define a function that takes two
arguments, and (sometimes) returns a `normal' form of the expression 
formed with that operator.  (This doesn't allow us to trace reduction
sequences -- we turn to that later.) The definitions correspond to the
transitions of an arithmetical machine. 

\begin{code}
infixr 8  <^> 
infixr 7  <*>
infixr 6  <+>
\end{code}

\begin{code}
(<+>),(<*>),(<^>) :: E -> E -> E
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
\end{code}

The following (partial!) function then evaluates an arithmetic
expression.

\begin{code}
eval :: E -> E
eval a   = case a of  b1 :+: b2    -> eval b1 <+> eval b2
                      b1 :*: b2    -> eval b1 <*> eval b2
                      b1 :^: b2    -> eval b1 <^> eval b2
                      _            -> a 
\end{code}



\section{Reduction sequences}

If an expression does not have a value, then the |eval| function
of the last section will not produce one, thank heavens.  Nevertheless, one
may want to observe finite segments of the sequence of reductions.  
We now write some code to make reduction sequences visible.

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
tlr e = case e of  (a :+: (b :+: c))   ->  [ (a :+: b) :+: c         ]
                   (a :+: V "0")       ->  [ a                       ]
                   (V "0" :+: a)       ->  [ a                       ]
                   (a :*: (b :+: c))   ->  [ (a :*: b) :+: (a :*: c) ]
                   (a :*: V "0")       ->  [ c0                      ]
                   (a :*: (b :*: c))   ->  [ (a :*: b) :*: c         ]
                   (a :*: V "1")       ->  [ a                       ]
                   (V "1" :*: a)       ->  [ a                       ]
                   (a :^: (b :+: c))   ->  [ (a :^: b) :*: (a :^: c) ] 
                   (a :^: V "0")       ->  [ c1                      ]
                   (a :^: (b :*: c))   ->  [ (a :^: b) :^: c         ]
                   (a :^: V "1")       ->  [ a                       ]
                   (a :^: b :^: V "+") ->  [ b :+: a                 ]
                   (a :^: b :^: V "*") ->  [ b :*: a                 ]
                   (a :^: b :^: V "^") ->  [ b :^: a                 ]
                   (a :^: _ :^: V "0") ->  [ a                       ]
                   _                   ->  [                         ]
-- v0 = V "0 "
v1 = V "1"    -- |v0 :^: v0|
-- c1 = error "Damn!" :^: c0
\end{code}

To represent subexpressions, we use a `zipper', in a form in which the
context of a subexpression is represented by a linear function.  We
represent each part |e| of an expression |e'| (at a particular
position) as a pair |(f,e)| consisting of the subexpression |e| there,
and a linear function |f| such that |f e = e'|.  (By construction, the
function is linear in the sense that it uses its argument exactly
once.) Intuitively you `plug' the subexpression |e| into the `context'
|f| to get back |e'|.

The function |sites| returns (in top down preorder: root, left, right \ldots) 
all the subexpressions of a given expression,
in the contexts in which they occur.  This includes the improper case of
the expression itself in the empty context. 
\begin{code}
sites :: E -> [(E->E,E)]
sites e   = (id,e) : case e of
                       (a :+: b) -> g (:+:) a b
                       (a :*: b) -> g (:*:) a b
                       (a :^: b) -> g (:^:) a b
                       _         -> []
            where g op a b =  [ ((a `op`) . f,p) | (f,p) <- sites b ]
                              ++ [ ((`op` b) . f,p) | (f,p) <- sites a ]
\end{code}

Now we define for any expression a list of the expressions to which it
reduces in a single, possibly internal step, at exactly one site 
in the expression.  This uses the function |tlr| to get
top-level reducts. 

\begin{code}
reducts :: E -> [ E ]
reducts a     = [ f a'' | (f,a') <- sites a, a'' <- tlr a' ]
\end{code}

We need a structure to hold the reduction sequences from an
expression.  So-called `rose' trees seem to be ideal.

\begin{code}
data Tree a = Node a [ Tree a ] deriving Show
\end{code}
We define a function which maps an expression to its tree of 
reduction sequences.

\begin{code}
redTree :: E -> Tree E
redTree e = Node e [ redTree e' | e' <- reducts e ]
\end{code}

To list the reduction sequences in a tree, individually or collectively is quite easy,
using the following function. 
It maps a tree to
a list (which may be infinite) of the sequences of
node labels encountered on some path to a node without descendants.
\begin{code}
branches :: Tree a -> [[a]]
branches (Node a []) = [ [a] ]
branches (Node a ts) = [ a : b | t <- ts, b <- branches t]
\end{code}












\fi
 
\section{Calculators and combinators}

In the dawn of functional programming, there were some working
implementations of combinator machines, using a complete set of
combinators such as $SK$, $BWCK$, or a variant thereof\footnote{For
  example: \cite{DBLP:journals/spe/Turner79} \cite{UCAM-CL-TR-81}
  \cite{UCAM-CL-TR-40}.  For implementing functional languages,
  attention quickly switched to supercombinators extracted from a
  particular program, but research on complete sets of combinators
  still continues,  if sporadically. TODO: cite some} .  If we count both paper and vapour implementations,
there were about a dozen.  One can daydream about
implementing `in hardware' a 
machine taking $AMEN$ as a basis. 
This would be an arithmetical calculator indeed~\footnote{In its ancestry there would be those 
cash-register-resembling desktop `adding machines' around
in the 1960's, and the pocket calculators of the 80's.},
handy to have in a pocket, or on a wrist.~\footnote{Lacking a silicon foundry, I wrote a small program to evaluate arithmetical
expressions built up from variables with constructors for addition, multiplication,
exponentiation, naught, and various constants.
This calculator uses algebraic laws to rewrite
expressions to arithmetical normal form.
I've found the calculator useful to avoid mistakes when
exploring and experimenting
with Naperian  arithmetic. Not only can one 
observe what combinators do, but it is also possible to check whether expressions are equal mod-$\zeta$.
}

To be remotely sensible, we should bake-into the calculator 
lots of binary combinators other than |(^)|,|(*)|,|(+)| and $(\ZERO)$.
Many familiar combinators show up everywhere, and deserve names. 
\footnote{A few examples:
\[\begin{array}{ccl}
\mbox{(i)} & (\sim) & \mbox{$ = C$ | = flip|}  \\
\mbox{(ii)} & (,)   & \mbox{for the pairing combinator} \\
\mbox{(iii)} & (\cdot), B & = (\times)^{(\sim)} \\
\mbox{(iv)}   & (+)^{(\sim)} & \\
\mbox{(v)}  & K & 0^{(\sim)} \\
\mbox{(vi)}  & (\$) & (\wedge)^{(\sim)} \\
\mbox{(vii)} & S & \mbox{and its flip\quad} S^{(\sim)}
\end{array}
\]


One observation is that
$(\wedge)$, $(\sim)$, $(,)$ and their flips
$(\wedge)^{(\sim)}$, $(\sim)^{(\sim)}$, $(,)^{(\sim)}$ 
are a handy 6-pack of combinators to permute the top 3 positions of
the arithmetical stack. Permutations are linear.
%
The combinators $(\ZERO)$ and $K = (\ZERO)^{(\sim)}$
are affine, or cancelative, \ie{} strip some entries from the stack.
%
The combinators $(+)$, $W$, $S = (\circ)$, $S^C = (\cric)$ (among many others,
for example those for operating on finite lists)
introduce sharing, contraction, diagonalisation, or other duplication: we cannot
perform their reduction in constant space, \ie{} during garbage collection.




%Maybe multiplicative lifting is a thing?
}

It makes no sense to ignore the associativity of addition and multiplication. So in such an arithmetical machine 
one might use `polyadic' forms of |sum| and |prod|, taking finite lists as arguments.
%\begin{spec}
\[ \begin{array}{lll}
  \sum  [a_1,..,a_k] &= a_1 + ... + a_k  \\
  \prod  [a_1,..,a_k] &= a_1 \times ... \times a_k  \end{array}
\]
%\end{spec}
The apparatus for lists is curious: the Church encoding of the
constructor to prefix a given item $x$ to a list $l$ is  $l + a^{(\wedge)}$.
the Church encoding of the empty list is $(\ZERO)$.
% This might help exploit the associativity of addition
% and multiplication.
Once one has lists, one should consider infinite streams, and co-lists.
How might $\sum$ and $\prod$ work
with infinite streams? One answer might be that the sum of a stream
is another stream, consisting of the accumulated finite partial sums, starting with 0.
The product might analogically consist of the accumulated finite partial products, starting with 1.
The idea is that a stream is turned into a stream of lists,
being the finite prefixes of the stream.

If one extends the arithmetical machine with streams, how should the operators behave when
one or other of their arguments are streams?
All I can say is that it is likely that, the operations $(a + )$, $(a \times)$, $(a \wedge)$ should distribute
over streams. The binary arithmetical operators are all continuous in their right-hand arguments. 
% 
% if done carefully.  Is there other scope
% for vectorising somehow?  Is it worth it?

To take this technological fantasy even further, consider graph rewriting
with `garbage collection', or recycling of otherwise wasted storage.
The fragment $MEI$ consisting of (exponentiation, multiplication and unity)
captures linear abstraction, and $MEN$ captures affine
abstraction.  It may be an advantage to easily recognise such features of an expression. 
For one thing, affine functions never introduce sharing, though they may discard garbage. The possibility of sharing 
requires constant care when rewriting graphs, and administering their storage. 
%However, there are other reasons to be interested in explicit linearity.
%Consider garbage collection (storage reclamation).
In graph reduction, the garbage collector (and not just the mutator) can
safely and beneficially perform certain `affine' forms of calculation -- \eg{} 
projections from tuples. 
See
%`Fixing some space leaks with a garbage
%collector' by Philip Wadler
\cite{wadler87fixing}.
%(Software Practice and Experience, 17(9):595-608, September 1987).
%It may be that more elaborate affine reductions than projections may %can 
%be performed by the garbage collector.

In some sense, an arithmetical calculator (a combinator machine for the
arithmetical combinators) would spend most of its time in
multiplicative (affine) mode, performing garbage collection.  From time to time
it would perform an addition, introducing sharing,
and thereby provoking more `multiplicative' work for the garbage collector.
Sums and not products would 
be the major headache for the designer of
the AMEN machine.~\footnote{This was pointed out to me by Conor McBride.}
%a long time ago;
%we have a conceit that his intellectual ancestor is
%Newton, with his differentiation and fluxions, 
%while I am strictly Naperian/logarithmorum.}



\section{Origins and heresies }

%Definitions of s
Slight variants of the arithmetical combinators abound
in the literature.  Some examples are in 
Rosenbloom 
(\cite[sec. 3.4]{rosenbloom50}
%: `The elements of mathematical logic', Dover 1950 ), 
Stenlund
(\cite[sec. 2.4]{Ste:comltp}
%: Combinators, lambda-terms and proof theory, Almqvist and Wiksell 1972, sec 2.4), 
and
Burge
(\cite[sec. 1.8]{burge75:_recur_progr_techn}
%: `Recursive Programming Techniques', Addison-Wesley 1975), 
They were surely defined by Church, and -- to stretch a point --
Wittgenstein (of whom, more anon). 
But in some sense we all know the definitions, if we understand
the concept of iteration at all.  They are in our brain-stems or DNA.
%go back to Archimedes.  

Of the authors mentioned above, as far as I know, only Stenlund notes
the combinatorial completeness of the arithmetical combinators.
In his thesis from 1972 he attributes the result to
F. B. Fitch.  He thinks he was made aware of it in correspondence with
some of Fitch's students. Apparently independently, B{\"o}hm was by
1977 aware of the combinatorial completeness
(\cite{bohm:1979},\cite{bohm:1981} -- written in 1977).  As already
mentioned, publication \cite{bohm:1981} (and presumably
\cite{bohm:1979}) notes the analogy between $\lambda$-abstraction and
logarithms referred to in section \ref{sec:log}, and in fact wrote the
logarithm function as $\lambda$ogarithm.  

\iffalse
B{\"o}hm in 
\cite{bohm:1981} also noted a few amusing arithmetical properties of the
combinators, such as that |C| is a square root of unity, \ie an involution\footnote{Are there any other non-trivial involutions?}.
A particularly interesting property
is 
\begin{spec}
   a ^ b = pr a * (b ^)   
\end{spec}
where |pr| is the code for the pairing function.  Using this B{\"o}hm is able
to define 
\begin{spec}
   log_x (a ^ b) = (log_x a) * pr + (log_x b) * (^)
\end{spec}
and to give a (less pleasing) expression for |log_x (a + b)|. 
\fi


% The algebraic structure of the arithmetical combinators seems too
% weak to be interesting. 


\paragraph{Repulsive variants of arithmetical notation:}

Many definitions of arithmetical combinators
get the argument order slightly wrong, in this author's opinion.  
They make the multiplication combinator the
same as the |B| composition combinator. This is a mistake. It should
take arguments the other way round.  
The business end of an arithmetical operation should always be the
second operand.
This mistake affects in turn the argument order
for addition, which is taken to be a pointwise-lifting of composition.  


To establish the scriptural correctness of my version, allow me to assert that
my definitions (at least for $\times$) can be read into
Wittgenstein's Tractatus (around 6.02 and 6.241).  The argument order has also 
the authority of Cantor according to whom the alternative is
`repulsive' -- absto{\ss}ende.  In fact Cantor started off using 
repulsive argument order, but soon thought better of it.  (This is
according to Michael Potter, \cite[p. 120]{potter90:_sets_introd}.)
In any case, the notation on which Cantor settled coheres attractively with
exponential notation for iteration, if we remember that multiplication is
composition in reverse:
\[
\begin{array}{llll} 
  f^{\alpha \times \beta} &= (f^\alpha)^\beta,  & \hspace{1cm}f^1 &= f, \\
  f^{\alpha + \beta}     &= f^\beta \cdot f^\alpha =  f^\alpha \times f^\beta ,  &  \hspace{1cm}f^0 &= 1\;. \\
\end{array}
\]
%In my opinion, the other way of writing |*| is repulsive.

  We leave the last word to Napier, from his note at the end of chapter 2 of book 1 of his \textit{Descriptio} :
\begin{quotation}
Indeed I await the judgment and censure of the learned men concerning these tables, before advancing the rest to be published, perhaps rashly, to be examined in the light of envious disparagement.
\end{quotation}

\iffalse
TODO: Something about recent interest in near-semirings, and related structures. 
Mauro Jaskelioff \cite{DBLP:conf/ppdp/RivasJS15},
Jeremy Gibbons \cite{ringads},
Tarmo Uustalu \cite{tarmo},
Statman \cite{Statman14}, \ldots.
%Uncle Tom Cobley, ... (Statman: "Near semi-rings and lambda-calculus" TLCA 2014 -- where \emph{does} the hyphen go??). 
Except for Statman (?) (and Mauro?), this is all at the level of types.
\fi

\bibliographystyle{alpha}
\bibliography{arithmetic}

\end{document}

