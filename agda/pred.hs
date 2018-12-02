{- Two definitions of the predecessor function on Church numerals -}
import Prelude hiding (fst, snd)

type E a = a -> a

type CN a = E (E a)

{-  KLEENE -}

type Pair f s r = (f -> s -> r) -> r

pr :: a -> b -> Pair a b r 
pr a b = \ c -> c a b

fst :: ((a -> b -> a) -> t) -> t 
fst p = p (\ x y -> x)

snd :: ((a -> b -> b) -> t) -> t 
snd p = p (\ x y -> y)

sComb a b c = a c (b c)
diag  f x   = f x x 

{- The most general type haskell infers....
pd
  :: ((((a2 -> b3 -> b3) -> a) -> (a -> b1 -> t1) -> t1)
      -> ((b -> b -> t2) -> t2) -> (a1 -> b2 -> a1) -> t)
     -> (a -> b1) -> b -> t

CN-oriented specialisation that we need
pd
  :: ( (((a -> a -> a) -> a) -> (a -> a -> a) -> a) ->
       ((a -> a -> a) -> a) ->
       (a -> a -> a) -> a
     )
     -> CN a 
-}


pd  :: CN (Pair a a a) -> CN a
pd n s z =  fst (n step start)
            where step p = let r = snd p in pr r (s r)
                  start  = pr z z
pdAlt  n s z =  fst (n step start)
                where step   = sComb pr s . snd 
                      start  = diag pr z 



test = let t n = n (+1) 0 in (t (pd zero), t (pd one), t (pd two), t (pd three))
zero, one, two, three :: CN a
zero = const id
one  = id
two f = f . f
three f = f . f . f
suc n f = f . n f
nos = iterate suc zero
testAlt = [ pd n (+1) 0 | n <- take 11 nos ]

{- Carrying out the test ..
λ> test
(0,0,1,2)
-}

{- OLEG KISELYOV'S -}

pd' :: CN (CN a) -> CN a
pd' n s z =  let step m g _ = g (m s z)
             -- g :: E a, m :: E (E a), step :: E (E (E a)), n :: E (E (E (E a))) 
             in n step zero id z

test' = let t n = n (+1) 0 in (t (pd' zero), t (pd' one), t (pd' two), t (pd' three))
{-
λ> test'
(0,0,1,2)
-}

{- CONTINUATIONS -}

type R = ()
type CT a = (a -> R) -> R

eta :: a -> CT a
eta a c = c a    -- ie eta = flip ($)  

join :: CT (CT a) -> CT a
mm `join` c = mm (eta c)
-- ie join mm = mm . eta = mm . flip ($) = mm `bind` ($)

bind :: CT a -> (a -> CT b) -> CT b
m `bind` f  = m . flip f
-- flip f :: (b -> R) -> (a -> R)
-- m :: (a -> R) -> R 

{- Encoding of Maybe a = a + 1 : (Pi X) (a -> X) -> X -> X   -}
type Mebby a x = (a -> x) -> E x  -- So Mebby x x = E (E x), by hackery.
nothing :: Mebby a x 
nothing _ n = n 

just :: a -> Mebby a x
just a j _ = j a

{- Let's rewrite OK's pd' -}

-- pd'' :: CN (CN a) -> CN a   There is a more general type ..
pd'' n s z =  let step m = just (m s z) 
              in n step nothing id z
test'' = let t n = n (+1) 0 in (t (pd'' zero), t (pd'' one), t (pd'' two), t (pd'' three))
