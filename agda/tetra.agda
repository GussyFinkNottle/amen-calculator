-- ALGEBRA TRANFORMATIONS 

-- explorations re tetration, predecessor and such things.

module tetra where

-- BASIC AMENITIES (very few used...)

  E E² E³ E⁴ : Set -> Set -- E is for Endo
  E X  = X -> X
  E² X = E (E X)
  E³ X = E (E² X)
  E⁴ X = E² (E² X)

  {- following belongs later -}

  {- We need someway to print largish numbers in a comprehensible way,
     like decimal notation. Uses a pragma of Agda. -}
  data G : Set where       -- G is for Ground
    zeG  : G
    suG  : G → G
  {-# BUILTIN NATURAL G #-} 
  -- the intention is have something that will print in decimal notation.
  -- we never case split on G and presume nothing about it but its two symbols
  base10 : E² G -> G 
  base10 n = n suG zeG

  {- combinators -}  --not all are used 

  {- identity -}
  id : { X : Set}-> E X                                   
  id {X} x = x

  {- constants -}
  const : { X : Set}-> {Y : Set}-> X -> Y -> X
  const x _ = x
  const' : { X : Set}-> {Y : X -> Set}-> (x : X) -> Y x -> X
  const' x _ = x

  {- composition -} 
  infixl 4 _∘_ 
  _∘_ : {X : Set} {Y : Set} {Z : Y -> Set} ->
          (f : (y : Y) -> Z y) -> (g : X -> Y) -> (x : X) -> Z (g x) 
  _∘_ {X} {Y} {Z} f g x = f (g x)
  infixl 4 _ø_     -- a more dependent version
  _ø_ : {X : Set} {Y : Set} {Z : Y -> Set} -> ((y : Y) -> Z y) -> (f : X -> Y) -> (x : X) -> Z (f x)
  _ø_ {X} {Y} {Z} f g x = f (g x)

  {- transposition -} 
  flip : {Z : Set}-> {B : Set} -> {A : Set}->
         (A -> B -> Z) -> B -> A -> Z
  flip  f b a = f a b
  
  {- standard "S" combinator (not used) -}
  cS : {X : Set}-> {Y : Set}-> {Z : Set}->
        (X -> Y -> Z) -> (X -> Y) -> X -> Z
  cS z y x = z x (y x)
  cS' : {X : Set}->                 -- dependent version
        {Y : X -> Set}->
        {Z : (x : X)-> Y x -> Set}->
        ((x : X) -> (y : Y x) -> Z x y) ->
        (f : (x : X) -> Y x) ->
        (x : X) -> Z x (f x)
  cS' z y x = z x (y x)             -- same definition
  -- some asymmetric infix notation for 'S' type combinators:
  -- the head of the arrow points at the preponent.
  _▷_  = cS               -- some infix notation for S and C S.
  _◁_  : {X : Set}-> {Y : Set}-> {Z : Set}->     
        (X -> Y) ->  (X -> Y -> Z) -> X -> Z
--  _◁_  {X} {Y} {Z} = flip {X -> Z} {X -> Y} {X -> Y -> Z} (cS {X} {Y} {Z}) 
  _◁_  = flip cS' 

  -- most general type of zero
  zero_gen : {X : Set}-> {Y : Set}-> Y -> E X
  zero_gen {X} {Y} = const id  -- const {X} {Y} (id {X})
  zero_gen' : {X : Set}-> {Y : X -> Set}-> (x : X)-> Y x -> X 
  zero_gen' = const' 



  -- Continuations. Probably unused
  _<-_ : Set -> Set -> Set
  X <- Y = Y -> X
  C : Set -> Set -> Set
  C X A  = X <- (X <- A)  -- continuation monad (result type X) C A = (X <-)² A
  A : (Set -> Set) -> Set -> Set -- E² Set
  A F X = C X (F X)   -- type of F-iterators over R.
{- remarks 

   When F X is X + 1, A F X is isomorphic to the usual Church numerals E² X.

   Notice (A <-) is contravariant, so (A <-)² is covariant.
-}


  -- the continuation functor
  mp : {R : Set}-> {A : Set} -> {B : Set} -> (A -> B) -> C R A -> C R B
  mp {R} {A} {B} f cra b2r =
        let a2r :  A -> R
            a2r a = b2r (f a) 
        in cra λ x → b2r (f x) -- (b2r ∘ f)
  -- the continuation monad
  et : {R : Set}-> {A : Set} -> A -> C R A
  et {R} {A} a k = k a
  mu : {R : Set}-> {A : Set} -> C R (C R A) -> C R A
  mu {R} {A}
     M k = let ek : ((A → R) → R) -> R
               ek = et {R} {A → R} k
           in M ek


  -- real world church numerals
  
  CN : Set₁       
  CN = {X : Set}-> E² X 

{- These are predicative church numerals. The quantifier may not be
instantiated by CN itself, for size reasons.
-}

{-
E (E X) is isomorphic to the type (S X->X)->X,
where S is the "maybe" or "opt" functor: S X = X + 1.
(s : E X, z : X |-> r s z)  : E (E X) corresponds sz |-> r (fst sz) (snd bsz).
r : (S X -> X) -> X corresponds to (s : E X, z : X |-> r [s|z])

This has to do with how algebras are represented. 

A Church Numeral polymorphically assigns to any set X, and any S-algebra on X,
an element of the carrier X.

Examples.
-}

{- these are here mainly to name some CN's when testing -}
  -- zero one. -- Don't constrain types.
  zero one : CN
  two three four five six seven eight nine ten : CN
  zero      = const id -- flip const -- zero_gen 
  one {X}   = id 
  two f     = f ∘ f        -- note the primes and powers
  three f   = f ∘ f ∘ f 
  four      = two two 
  five f    = two f ∘ three f
  six       = two ∘ three
  seven f   = three f ∘ four f
  eight     = three two
  nine      = two three
  ten       = two ∘ five
  succ : CN -> CN
  succ n {X} f = f ∘ (n {X} f)

{-
Arithmetic on Church Numerals.
-}

  infixr 2  _+_
  infixr 3  _*_
  infixr 4  _^_
  infixr 5  _^^_
--  infixr 6  _^^^_

  _+_  _*_  _^_  : CN -> CN -> CN
  (a + b) {X} s z   =  b {X} s (a {X} s z)         -- : X
  (a * b) {X} s     =  b {X} (a {X} s)             -- : E X
  (a ^ b) {X}       =  b {E X} (a {X})             -- : E (E X)
--  (a ^ b) {X} s z  =  b {E X} (a {X}) s   z

  O I   : CN                  -- more concise notation 
  O {X} = zero -- _ z  = z
  I {X} = one 

-- We have the means to write some large Church numerals

  t tt ttt tttt : CN
  t = two   -- actually exp2 (exp2 0) = exp2 1 
  tt {X} = t {E X} (t {X})       -- 2^2  = 4
  ttt {X} = (tt {E X}) (t {X})   -- 2^4  = 16
  tttt {X} = (ttt {E X}) (t {X}) -- 2^16 = 65536

-- Here we iterated exp2, starting with 2
  exp2 : CN -> CN
  exp2 n {X} = n {E X} (two {X})

  t' tt' ttt' tttt' : CN
--  t' {X} = exp2 zero (exp2 (exp2 zero))  -- exp2 zero (t {X})
  t'    = exp2 (exp2 zero)  -- exp2 zero (t {X})
  tt'   = exp2 t'
  ttt'  = exp2 tt' 
  tttt' = exp2 ttt' 

  {- 
     At this point, we would like to make the process
     of writing down successive numbers more feasible,
     by using iteration.  
  
     We get a size error Set != Set₁ when checking that
     exp2 is something that can be iterated

  f : CN -> CN
  f n = n step start
        where start = two
              step = exp2 -- {!!} -- exp2 {!!} 

  -}

  {- Initial explorations.
     Most of this is redone in a more general way later on.
  -}
  mutual -- a hierarchy of "pure" sets on G
    data U₀ : Set where
         g : U₀ 
         e : U₀ -> U₀
    T₀ : U₀ -> Set     
    T₀ g = G
    T₀ (e n) = E (T₀ n)

  scn : Set    -- small Church numerals
  scn = (u : U₀)-> E² (T₀ u) -- (n : U₀)-> T₀ (e (e n))

  sone stwo : scn
  sone u = one -- { T₀ u }
  stwo u = two { T₀ u }

  shrink : CN -> scn
  shrink n u = n { T₀ u }

--  at2 : scn -> scn
--  at2 t u =  t (e u) (two { T₀ u })
  at  : scn -> scn -> scn    -- exp
  at n t u = t (e u) (n u)
  at'  : scn -> scn -> scn   -- mul
  at' n t u s = t u (n u s)
  at''  : scn -> scn -> scn  -- add
  at'' n t u s z =  t u s (n u s z)
  

-- now we can iterate with carrier scn instead of the impredicative type.

  tetr : scn -> CN -> scn -- cf   _^_ : X -> E X -> X
--   tetr : scn -> E (E scn) -> scn  
  tetr m n =  n {scn} (at m) (shrink one) -- g
  tetr' : scn -> E² scn -> scn  -- slightly more "logical", perhaps.
  tetr' m n =  n (at m) m -- n {scn} (at m) m -- g
  _^^_ : scn -> E (E scn) -> scn
  m ^^ n = tetr' m n

  printCN : CN -> G
  printCN n = base10 (n {G})

  sprint : scn -> G
  sprint n = base10 (n g) 

  test-tetr test-tetr' : CN -> CN -> G --24-1 test24-2 : G  -- both print 65536
  test-tetr  m n = sprint (tetr (shrink m) n)  
  test-tetr' m n = sprint (tetr' (shrink m) n)

{- The process we are trying to formalise.
   We have a binary function f : X -> E X. 
   We form from it  

       F f  =   n x |-> (f x)^n x : E² X -> E X

   We would like to iterate F starting with exponentiation.
   So we have somehow to make E (E X) and X "the same",
   polymorphically -- we need a carrier. 

-}

{- Notes on tetration.
   Keywords: Knuth, Goodstein, hyperoperation.
   Each operation in the whole sequence of hyperoperations
   is primitive recursive, but not the sequence itself. 
   For that, the iteration needs to occur at a higher type.

   We define 
   m ^^ 0 = m
   m ^^ (n+1) = m ^ (m ^^ n)
 
  So (m ^^) is the series m , m ^ m , m ^ (m ^ m), etc.
  (m ^^) n = (m ^)^n m 

  Eg (2 ^^) = 2 = 2^^0, 
              4 = 2^2 = 2^^1, 
              16 = 2^4 = 2^^2, 
              65536 = 2^^3

    (3 ^^)  = 3, 27, 3^27 = 7625597484987

  We are clearly iterating an operator on binary functions,
so the iterator needs type E^2 (N -> N -> N). 
-}

-- Interlude on things that are not fast-growing: SIGNUM 

  -- These are conventional names: sg comes from "signum", it seems.
  -- sg _ s z    (as a stream) is z,sz,sz,sz,... = 0;rep 1
  -- sgbar _ s z (as a stream) is sz,z,z,z...    = 1;rep 0
  -- some equations:
  -- sgb . sgb = sg . sg = sg
  -- sgb . sg = sg . sgb = sgb

  sg sgbar : CN -> CN    -- these are iterable. No type shift is needed.
  sgbar b {X} s z  = b {X} (const {X} {X} z) (s z)  
  sg    b {X} s z  = b {X} (const {X} {X} (s z)) z  

  sg' sgbar' : CN -> CN  -- these are not iterable.
  sgbar' b {X} = b {E X} (O {X})   -- zero to the power b 
  sg'  b  = sgbar' (sgbar' b)
--  sg'    b {X}  = sgbar' (sgbar' b {X}) {X}

  psg psgbar : {X : Set}-> E³ X    -- E² X -> E² X
  psgbar n f z = n (const z) (f z)
  psg    n f z = n (const (f z)) z

  parity : {X : Set}-> E⁴ X -> E² X
  parity {X} n = n psgbar O 

  -- need bounded sum, of parity function -- step =  (λ e2x ex x → e2x (const x) (ex x))
  div2    : {X : Set}-> E⁴ X -> E² X   -- this is actually an implementation of parity! 
  div2 {X} n  = n step' (zero {X})
                where step' : E³ X -- ² X -> E X -> X -> X 
                      step' e2x ex x = e2x (const {X} {X} x) (ex x)
                      
-- PREDECESSOR AND SUCHLIKE

  pd' : {X : Set}-> E⁴ X -> E² X -- same type as parity
  pd' n s z = n (λ m f _ → f (m s z)) zero id z

  pd : CN -> CN
  pd b {X} = pd' ( b {E (E X)}) 

  -- cons a f = (a <| f) is (\n->if n==0 then a else f (n-1)), ie. [a,f0,f1,f2,...]
  -- so pd should be cons 0 id
  --    sg should be cons 1 (const 0)
  --    sgbar should be cons 0 (const 1)
  -- cons 88 df =  [88,df0,df1,df2,...]

  -- this very preliminary.  I take a "function" to be of type E³ X, which of course
  -- is very restrictive. successor has that type, it's finite composites too, and
  -- polynomials like x |-> x² + 2x + 1 (see what-about below), ...


  cons : {X : Set} -> E² X -> E³ X -> E⁴ X -> E² X 
  cons {X} a f n s z
    = let postponent : E² X -> X 
          postponent = (λ x ->  x (a s z)) ∘ (λ x -> x id) 
          iteration : E⁴ X -> E² X 
          iteration n = n (λ m g _ → g (f m s z)) zero
      in  postponent (iteration n)
  infixr 3 _|>_
  _|>_ = cons

  -- if we reorder the arguments, the type becomes simpler.
  snoc : {X : Set} -> E (E² (E² X))
  snoc {X} n f a s z
    = let postponent : E² X -> X
          postponent = (λ x ->  x (a s z)) ∘ (λ x -> x id) 
          iteration : E² (E² X) → E² X
          iteration n = n (λ m g _ → g (f m s z)) zero
      in  postponent (iteration n)
  infixr 3 _<|_
  _<|_ = snoc 

{-
Possible task:
Try to code (n mod m). Note that (0 tetra n) is (n mod 2). Ish.
See Mateusz Zakrzewski: Definable Functions in the Simply Typed λ-Calculus

The mod function is not an extended polynomial, because it is not
eventually non-decreasing. A particular case is the parity function,
that is an instance of tetration.

-}

{-
At some point, check everything works smoothly with 
"dependent-church"-encoding, as in:

  Set^ : Set -> Set₁
  Set^ A = A -> Set

  CNN : CN -> Set₁
  CNN a
      = {X : Set}     ->  {X' : Set^ X} ->
        (s : X -> X)  ->  (s' : (x : X)-> X' x -> X' (s x))->
        (z : X)       ->  (z' : X' z)->
        X' (a {X} s z)

-} 

{- GAS. Probably for an intro.

A particularly simple type-theory with function or arrow types is one
in which the the domain and codomain of any function are the same type, so that the
function is iterable.  
So one has arrow types, but only in "diagonal" form E X = X -> X.  

Types of this kind have been called "pure" types, counted of as 0 = ground type X, 
type 1 = E X, type 2 = E X -> X etc. 
Type 2 might alternatively be E² X, etc with level n being 
(Y |-> Y -> X)ⁿ X or Eⁿ X respectively.  

If X is equipped with pairing apparatus,
pure types above X have an intricate structure of sections and retractions, sufficient to encode less regimented forms of function space into pure types. 
In other words, pure types "have" products, for some value of "have". 

Such an austere type-theory, with its arrow operator in this restricted form,
has nevertheless almost incredible notational power. It can
be used to provide compact, surveyable, well-typed notations 
for some unfeasibly large numbers: meaning numbers whose unary representation 
using grains of sand for each successor would fill the known universe.  

In a sense, this power was
demonstrated by Archimedes, 
the inventor of exponentiation in an iterable form.

Besides providing compact notation for huge numbers, the type-theory
gives a compact notation for writing programming numerical functions,
that produce the right answers, in some cases in a few seconds.
Yet these functions can have stupendous growth-rate, and even when
they don't, their computation may place insatiable demands on resources.

A Church numeral is a proof of G given a type G and axioms o : G
s : G -> G; we consider numerals up to alpha-equivalence (So G, o, s
are schematic variables.) It is a syntactic object, in the 
metalanguage. It can be instantiated at any type we like.

For example, take the simply-typed lambda-calculus. This
allows us to write Church numerals. We might say that a
representation of a unary numerical function f is a closed
term t_f such that, if [n] denotes the n-th Church numeral,
then for all n, [f n] = t_f [n]. 
This is an "internal" representation.

An external representation is by a structure in the metalanguage,
that may involve type operations, such as E, and operations that
transform algebras for S X = X + 1, (ie. carriers X, and structure
maps x : S X -> X ) into (1) structure maps (u x) : S (E X) -> E X
for the carrier (E X) and (2) projection maps (d x) : E X -> X. 
The following equation should hold uniformly for any carrier X
and algebra sz : S X -> X: 

   fold {X} sz . f  = d {X} sz . fold {E X} (u sz) 
                    : Nat -> X

That is to say, there are syntactical entities that represent
numbers (namely iterators, or Church numerals), and 
numerical functions (namely transformations of algebras). 
The representation is such that we can in principle calculate
the value of a representable function at an arbitrary argument. 

Due to Schwichtenburg, we know that the numerical functions
representable in the STLC are precisely the extended polynomials.
The extended polynomials are built up from basic functions like
the identity, projection and constant functions by addition
and multiplication, and crucially the function $0^x$.

All extended polynomials are eventually non-decreasing. So
for example the function that assigns to a number its parity bit
is not an extended polynomial - it decreases (and BTW increases) infinitely often.
[Interestingly, tetration can be used to define the parity function.]
Similarly the function mod-24, that cycles infinitely through the numbers 0,1,..,23 
is not eventually non-decreasing.

Nevertheless, the extended polynomials embody "feasible computation"
in some narrow sense. They are "as bad as it gets" in terms of 
computational resources like memory and time. The size of the resources required
are at worst some polynomial of the size of an argument.

-}

  mutual                 -- this should probably be expressed with a module
    data N : Set where
         s : N -> N
         o : N 
    It : N -> (Set -> Set) -> Set -> Set     
{-  size issues with ∘ and id:
    It (s n) step  = step ∘ (It n step)
    It o     _     = id 
-}
    It (s n) step  start = step (It n step start)
    It o     _     start = start
    -- this is the only case split in the entire file.

  -- produces an infinite product. Call it omega?
  w w' w'' : (F : Set -> Set)-> (X : Set)-> Set
  w   F X = (n : N)-> It n F X              -- simplest. Doesn't work some reason.
  w'  F X = (n : N)-> E² (It n F X)         -- "little" church numerals
  w'' F X = (n : N)-> E X -> X -> It n F X  -- unexplored

  infixr 7 _`e`_
  infixr 6 _`m`_
  infixr 5 _`a`_

  exp _`e`_ : {X : Set}-> X -> E X -> X  -- this what we start with
  exp a b = b a                    -- use some infix symbol..
  _`e`_   = exp
  
  mul _`m`_ : {X : Set}-> E X -> E² X
--  mul a b = b ∘ a
  mul a b x = (x `e` a) `e` b
  _`m`_ = mul 

  add _`a`_ : {X : Set}-> E² X -> E³ X
--  add a b x = (b x) ∘ (a x) 
  add a b x = (x `e` a) `m` (x `e` b)
  _`a`_     = add  

  oh : {X : Set}-> E² X 
  oh _ = id

  what-about what-about' : {X : Set} -> E² X -> E² X
  what-about {X} n = (n `m` n) `a` (n `a` n) `a` id -- n² + 2n + 1
  what-about' {X} n = let n² = n `m` n
                          n³ = n² `m` n
                          3n² = n² `a` n² `a` n² -- add (add n² n²) n²
                          3n  = n `a` n `a` n -- add (add n n) n
                      in n³ `a` 3n² `a` 3n `a` id   -- n³ + 3n² + 3n + 1


  -- make exp into something homogeneous in both arguments
  exp=' : {X : Set} -> let r = w' E X in r -> r -> r 
  exp=' {X} a b n =  exp {E² (It n E X)} (a n) (b (s n))
  exp= : {X : Set} -> let r = w E X in r -> r -> r   -- abandoned variant
  exp= {X} a b n =  exp {It n E X} (a n) (b (s n))

  -- now we can iterate it, with a suitable church numeral
  tet' : {X : Set}-> let r = w' E X in r -> E² r -> r 
  tet' {X} a b = b (exp=' a)   (λ n  → one {It n E X}) -- {It n E X}) 
  tet : {X : Set}-> let r = w E X in r -> E² r -> r  -- abandoned variant
  tet a b = b (exp= a) a  

  coerce : CN -> {X : Set}-> {F : Set -> Set}-> w' F X
  coerce cn {X} {F} = \n -> cn { It n F X }

  {- these seem to go with dd below. Mostly unused. -}
  suc : { X : Set}-> E (E² X)
  suc n f = f ∘ n f                     -- or the other way round
  squish : {X : Set}-> E² (E² X) -> E² X   -- like monad multiplication
  squish {X} mm  = mm (suc {X}) (O {X})
  eta : {X : Set}-> X -> E² X           -- is this any use?
  eta {X} x _ _ =  x   
  chk : {X : Set}->    -- check for definitional equality
        {X' : E² X -> Set}->
           X' (squish {X} (ten {E² X})) -> -- (ten {M X} suc nil) ->
           X' (ten {X})
  chk = id 

  ss : {F : Set -> Set} {X : Set}-> E (w' F X)
  ss {F} {X} a =  \n -> suc {It n F X} (a n)
  
  zz : {F : Set -> Set} {X : Set}-> w' F X 
  zz {F} {X} = coerce O -- zero                                 -- (λ n  → zero { It n F X } )

  -- the following operation seems to be important. An absorption. 
  dd : {F : Set -> Set} {X : Set}-> E² (w' F X) -> w' F X
  dd x = x ss zz


  test-tet' : CN -> CN -> G   -- prints as a decimal number.
  test-tet' m n
         = let ans : w' E G 
               ans = tet' (dd (m {w' E G})) 
                              (n {w' E G}) 
           in base10 (ans o)

{- For example, ^C^N (to invoke normal form evaluation)
   and then evaluating  

       expression                        print output
       ----------                        ------------
       test-tet' two four                65536 (after some delay).
       test-tet' zero zero               1
       test-tet' zero one                0
       test-tet' zero two                1     etc
-}




{-
Now the problem is to get a suitable church numeral homogeneously.
-}

  tet= : {X : Set}-> let r = w' (w' E) X 
                     in r -> r -> r 
  tet= {X} a b n =  let -- just to show what is going on...
                        bsn : E² (w' E (It n (w' E) X))
                        bsn = b (s n) 
                        an : E² (It n (w' E) X) -- E² (It n E {!!}) 
                        an = a n
                        y : w' E (It n (w' E) X)
                        y = tet' (dd (a (s n))) (b (s n)) 
                    in y o 

--  coerce1 : CN -> {X : Set}-> w' (w' E) X
--  coerce1 cn {X} i = cn { It i (w' E) X }

  test-tet= : CN -> CN -> G -- (n : N) → E² (It n (w' E) G)
  test-tet= m n = base10 (tet= (coerce m) (coerce n) o) 
  
-- -}

  {- Pentation -}
  pent : {X : Set}-> let r = w' (w' E) X in r -> E² r -> r
  pent {X} a b = let x : E (w' (w' E) X)
                     x = b (tet= a)
                     y : w' (w' E) X                  -- (n : N) → E² (It n (w' E) X)
                     y = coerce one                   -- λ n  → one {It n (w' E) X}   -- coerce?
                 in x y

  pent= : {X : Set}-> let r = w' (w' (w' E)) X in r -> r -> r
  pent= {X} a b n =
       let
          bsn : E² (It (s n) (w' (w' E)) X)
          bsn = b (s n)
          an : E² (It n (w' (w' E)) X)
          an = a n
          y : w' (w' E) (It n (w' (w' E)) X)
          y = pent (dd (a (s n))) (b (s n))
       in y o

  pent=a : {X : Set}-> let r = w' (w' (w' E)) X in r -> r -> r
  pent=a {X} a b n = pent (dd (a (s n))) (b (s n)) o

  test-pent= : CN -> CN -> G
  test-pent= a b = let
                    ans = pent= (coerce a) (coerce b)
                  in base10 (ans o)

-- some little explorations ....
-- connected with the type-operator "(+1)", aka Maybe X = Just X | Nothing
-- This operator is in the background of pd.

  M : Set -> Set                -- M because it's slightly monadic...
  M X = E² X                    -- because it has a multiplication muM.
                                -- ("squish" elsewhere)
  opt : {X : Set}-> X -> M X       -- eta
  opt  x  =  const ∘ (λ f → f x)   -- just x j _ = j x
  nil : {X : Set}-> M X            -- zero
  nil = const id                   -- nothing _ n = n 
  exM : {X : Set}-> M X -> E X -> E X
  exM m = m

  muM : {X : Set}-> M (M X) -> M X
  muM mm = mm suc zero

  -- this is just for comparision with the above
  data M' (X : Set) : Set where nil' : M' X      
                                opt' : X -> M' X  -- etaM'
      -- the following use "cases", without any recursion
  exM' : {X : Set}-> M' X -> E X -> E X
  exM' nil'     _ z = z                -- nil' = const id
  exM' (opt' x) f _ = f x          -- just' x = f |-> const (f x)

  muM' : {X : Set}-> M' (M' X) -> M' X -- USES CASES (but not recursion).
  muM' nil'     = nil'
  muM' (opt' z) = z
                                

  pd99 : {X : Set}-> E² (M X) -> E² X
  pd99 {X} n f z
             = let step : E³ X 
                   step m = opt (exM m f z)
               in exM (n step nil) id z

  pd99' : {X : Set}-> E² (M' X) -> E² X
  pd99' {X} n f z
              = let step : E (M' X) 
                    step m = opt' (exM' m f z)
                in exM' (n step nil') id z

  pd99= : {X : Set}-> let r = w' M X in r -> r
  pd99= {X}
        a n = let -- Xn : Set
                  -- Xn = It n M X
                  -- an : E² Xn 
                  -- an = a n
                  -- asn : E² (M Xn) 
                  asn = a (s n)
              in pd99 asn

  test-pd99= : CN -> G
  test-pd99= n = let x : (n₁ : N) → E² (It n₁ M G)
                     x = pd99= (λ i → n { It i M G })
                 in base10 (x o)

  {- cutoff subtraction, unbalanced form -}
  _∸_ : {X : Set}-> let r = w' M X  in r -> M r -> r
  a ∸ b = b pd99= a

  test∸ : CN -> CN -> G
  test∸ m n = let
                    x : w' M G
                    x = (λ i → m {It i M G}) ∸ n {w' M G}
                  in base10 (x o)

  {- Now the problem is to make a homogeneous version of ∸ -}
  sub= : {X : Set}-> let r = w' (w' M) X
                     in r -> r -> r
  sub= {X} a b n = let
                     an : E² (It n (w' M) X) -- just for interest
                     an = a n
                     bsn : E² (w' M (It n (w' M) X))  
                     bsn = b (s n)
                     x : w' M (It n (w' M) X)
                     x = dd (a (s n)) ∸ bsn
                   in x o

  -- absolute difference | a - b | = (a ∸ b) + (b ∸ a)
  adiff : {X : Set}-> let r = w' (w' M) X in r -> r -> r 
  adiff {X} a b 
              =  let l : (n : N) → E² (It n (w' M) X)
                     l = sub= a b
                     r : (n : N) → E² (It n (w' M) X)
                     r = sub= b a
                     _+_  : {X : Set} -> E² X -> E³ X 
                     (m + n) f = n f ∘ m f 
                 in λ n -> l n + r n 

  -- equality iszero |a - b|
  eq : {X : Set}-> let r = w' (w' M) X in r -> r -> r 
  eq {X} a b 
              =  let l : (n : N) → E² (It n (w' M) X)
                     l = sub= a b
                     r : (n : N) → E² (It n (w' M) X)
                     r = sub= b a
                 in  -- {!psgbar ø adiff l r!} --
                     λ n  → psgbar (adiff l r n)  -- λ n f z   → r n f (l n f z)

  _>_ : {X : Set}-> let r = w' (w' M) X in r -> r -> r 
  _>_ {X} a b 
              =  let l : (n : N) → E² (It n (w' M) X)
                     l = sub= a b
                     r : (n : N) → E² (It n (w' M) X)
                     r = sub= b a
                 in λ n  → psg (l n) --  (adiff l r n)  -- λ n f z   → r n f (l n f z)

  _<_ : {X : Set}-> let r = w' (w' M) X in r -> r -> r 
  _<_ = flip _>_

  -- boolean calculus
  _&_ _v_ _=>_ : {X : Set} -> E² X -> E³ X
  not : {X : Set} -> E³ X
  _&_  a b         = a ∘ b 
  a v b            = psg (λ f  → a f ∘ b f) 
  _=>_  a b f z    = a (const (b f z)) (f z)
  not p f z        = p (const z) (f z)

--  coerce2 : CN -> {X : Set}-> w' (w' M) X
--  coerce2 cn {X} i = cn {It i (w' M) X}
--  coerce2 cn {X} = coerce cn {X}  -- cn {It i (w' M) X}

  test-sub= : CN -> CN -> G
  test-sub= a b = let
                    ans : w' (w' M) G 
                    ans = sub= (coerce a) (coerce b)
                  in base10 (ans o)

  test-adiff : CN -> CN -> G
  test-adiff a b = let ans : w' (w' M) G
                       ans = adiff (coerce a) (coerce b)
                   in base10 (ans o)

  test-eq : CN -> CN -> G
  test-eq a b = let ans : w' (w' M) G
                    ans = eq (coerce a) (coerce b)
                in base10 (ans o)
  test-< : CN -> CN -> G
  test-< a b  = let ans : w' (w' M) G
                    ans = coerce a < coerce b
                in base10 (ans o)
  test-> : CN -> CN -> G
  test-> a b  = let ans : w' (w' M) G
                    ans = coerce a > coerce b
                in base10 (ans o)

{- talk-abstract 
Primitive-recursion done with very weak predicative universes

Schwichtenberg 76(?) showed that the numerical functions definable/denotable by
closed terms of the simply typed lambda calculus 
(NB: no ground type of Natural numbers) are precisely the 
"generalised polynomials".

Generalised polynomials are defined from linear functions 
(say what this means), sg, and sgbar
by addition, multiplication and composition. 

One non-example is the parity function,
others are exponentiation and predecessor.  
These functions *can* be represented in a
more liberal sense by certain metamathematical objects, in which
type-operations such as (X |-> X->X = the diagonal of the arrow) 
play a key role.  

However, to iterate such operations (to define tetration from exponentiation, 
or subtraction from predecessor) internally needs universes that are closed under 
the relevant type operations.  I'll show a way to denote/represent all the primitive
recursive functions, by iterating (externally) a type-2 universe operator. 
Some discussion of what exactly is universal about my universes may be attempted.

Someone impetuous might even conjecture that all (numerical) functions definable in Godel's T remain definable 
when Nat is replaced with inexhaustible many higher levels of universe operators, beyond level-2.
-}

{- What is a universe? 
 
  The most characteristic feature of the universes we are familiar with
  is that the type-declarations that introduce the various forms of the 
  elements of the universe U make mention of an ancillary function
  T defined on U.  T is defined by iteration, and cannot involve U. It is
  not available.

  If the set U is a universe of *sets*, then the values of T will be sets 
  -- but the elements of U could denote operators on types, possibly
     of higher order. This called "large IR". (Uppercase "T".)
  -- On the other hand, the elements of U could denote elements of
     some existing set.  This is called "small IR". (Lowercase "t".)

  It may be uncharacteristic, but there is no reason or requirement that
  the introductory clauses should make mention of the ancillary function T.  
  or depend on it in any way. This is called (by me) "iterates for free".
  The point is that the iterates can be large (or small). 
  Another term is (I use) is "degenerate IR". 
  (Which me reminds of Nazi art exhibitions.)

  The introductory clauses for a universe may, or may not be taken to
  be exhaustive. 
  -- One might anticipate adding other forms of element should the need arise.  
  -- One might simply postulate new elements
  -- On the other hand, one might want to postulate something even stronger
     namely that all elements of U are accessible, 
     in the sense that they have a well-founded construction
     supporting the definition of functions by structural recursion.

  What is a universe really?  

  There are two kinds.
  The first is a type, together with a dependent family of types.
  We might write the type Set, and if i : Set, might write the i-th member 
  of the family as El i. 
  We postulate that Set is closed under certain syntactical operations that
  denote operations on types of the form El i. We set up a an inner type theory.
  This is a ground family in the outer type theory. 

  The second kind is a Grothendieck universe.  This is a particular set. 
  It lives in Set, and it comes with a function that produces Sets from its
  elements.  U : Set.  T : El U -> Set.

-}


{- try something else. A universe with arrow and times -}
  mutual   
    data N' : Set where
         _to_ : N' -> N' -> N'
         _ti_ : N' -> N' -> N'                         -- or maybe finite lists
         o' : N'
    It' : N' -> (Set -> Set -> Set) -> (Set -> Set -> Set) -> Set -> Set
    It' (m to n) stepto stepti start = stepto (It' m stepto stepti start) (It' n stepto stepti start)
    It' (m ti n) stepto stepti start = stepti (It' m stepto stepti start) (It' n stepto stepti start)
    It' o' _ _ start = start
    -- our only case split in the entire file.

  e' ee' p' : N' -> N'
  e' n = n to n       -- endomorphisms
  p' n = n ti n       -- endopairs
  ee' n = e' (e' n)   -- church numerals at n
  ω : (F : Set -> Set -> Set)->
      (G : Set -> Set -> Set)->
      (X : Set)-> Set
  ω F G X = (n : N')-> It' (ee' n) F G X 

