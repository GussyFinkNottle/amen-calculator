  import Prelude hiding (exp)


  
--   pd : Nat (Nat a) -> Nat a

{-
  Here, in raw form, is Oleg's version of the predecessor function:
-}

  type E x = x -> x
  type E0 x = x
  type E1 x = E x
  type E2 x = E (E x)
  type E3 x = E (E2 x)
  type E4 x = E (E3 x)

  type N x  = E2 x
  pd n s z = n (\ m f _ -> f (m s z)) (const id) id z
  pd :: N (N x) -> N x

{-
This is pretty inscrutable.  It may be easier to understand
if we make it explicit that we are really iterating an operator on a "Maybe" type.
We start with the nil(/zero), and we iterate the operator that
returns always a just-element, whose content is of ground type,
and is got by eliminating its argument over s and z.
When we have iterated enough, we eliminate from the
maybe element (using the identity to process Just elements,
and z as default in the Nil case) to get something of
ground type x.

-}

  --  mayBe m f z = m f z
  mayBe       = id
  just x f    = const (f x)
  nil         = const id 

  type M x = E2 x
  mayBe :: M x -> E x -> x -> x
  just  :: x -> M x 
  nil   :: M x     -- actually y -> E x

  pd_explicit n s z = mayBe ( n (\ m -> just (mayBe m s z)) nil
                          ) id z
  pd_explicit :: N (N a) -> N a

{-
Oleg's predecessor cries out to be generalised.  It provides
us with the means to define an operator that "pushes" a given
number g on the start of a numerical function. That is to say,
it turns a function f = (a,b,c,...) into the function (a,f) = (g,a,b,c,...),
like a constructor on streams.
-}
  gpd a f n s z = mayBe (n (\m -> just (mayBe (f m) s z)) nil)
                        id (a s z)

  gpd :: E2 x -> E3 x -> E4 x -> E2 x

{-
This operation is easily inverted. This means we have some
apparatus for pairing a :: N x with f :: E(N x) to get g :: N(N x) -> N x 
To retrieve a, we use g 0, and to retrieve f, we use (g . suc).
Unfortunately, we cannot have g :: E(N x), where x is a ground type.

It is a shame. Using Haskell, one cannot iterate the predecessor
function, because its type is N(N x) -> N x rather than E of something.
We can write (pd (pd (pd two))), but we cannot write
(three pd two).
In the same vein, we can evaluate

      two two two two (+1) 0                   -- gives 65536

but not

      let t = exp two in (three t two) (+1) 0  -- "infinite type: b ~ b -> b"

Interestingly, even slow-growing functions (dominated by the identity)
incur this phenomenon of type-shifting from arguments to values.

To fix this, we are going to use some "universe" technology.
In the simplest case, a universe is a type U whose values
are arguments to a type-valued function T (a dependent type)
with domain U.  In fact we will need higher-order universe operators.
We use this technology to construct types of the form (E x) for operations
like pd, in order that pd can be iterated using a Church numeral.
(Cut-off subtraction [a - b] can then be defined by (b pd a).) 

-}

  sg n s z    = n (const (s z)) z
  sgbar n s z = n (const z) (s z)
  parity n    = n sgbar nil

-- E0 x is empty

-- E1 x is inhabited only by id 

-- E2 x is inhabited by the (remaining) Church numerals

-- E3 x is inhabited (additionally) by the extended polynomials
  sgbar, sg  :: E3 x            -- 1,0,0,0,...
  -- also suc, const n, \x -> x^3 + 3x^2 + ... etc.

-- E4 x -> E2 x is inhabited by
  parity     :: E4 x -> E2 x    -- 0,1,0,1,...
  -- also pd

{-
Note that if we want to define something like division by two,
we should probably first define "the bounded sum" of a function.

  bs n f  = Sum {i : [0..n) } f(i)

Then [n/2] = bs n parity.  Unfortunately bs itself exhibits the
phenomenon of type-shifting.  It's definition requires iterating
an operation on pairs, representing first an accumulated sum, then
the unprocessed part of the input function f.  So the argument n
will of necessity have a higher type than the value of (bs n f).
-}

  zero    = nil
  one     = id
  two f   = f . f
  three f = f . two f
  suc n s = s . n s
  add m n s = n s . m s
  mul m n   = n . m
  exp m n   = n m
  zero :: N a
  suc  :: E(N a)
  add  :: N a -> N a -> N a
  mul  :: E a -> E a -> E a
  exp  :: a -> E a -> a

  bs n f -- s z
         = accu (n step (init0 f))
{-           where -- accu g = g zero
                 -- fn   g = g . suc
                 init   = gpd zero f 
                 step g = let a = accu g ; f = fn g
                          in gpd (a `add` (f zero)) (f . suc)  -}

  accu :: E(N a) -> N a
--  accu g = g nil
  accu = exp nil 

  fn :: N(N a)   -- E(N a) -> E(N a)
--  fn g = g . suc
  fn = mul suc

  step :: E (N x) -> N (N x) -> N x
  step g  = let a = accu g ; f = fn g
            in gpd (a `add` (f nil)) (f . suc)

  init0 :: E (N x) -> N (N x) -> N x
  init0   = gpd nil
{-
  bs   :: ( ( E (N a) ->
              N (N a) -> N a
            ) ->
            ( N (N a) -> N a ) ->
            N x2 -> N a
          ) ->
          E (N a) -> N a
-}

  squash :: N (N x) -> N x
  squash n = n suc nil

