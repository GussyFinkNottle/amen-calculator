{-
Haskell explorations around bounded sum.
-}

{-
First, define it on the `ordinary' numbers.
-}

{-# LANGUAGE DeriveFunctor #-}
data N = Z | S N --
data Str a = Cons a (Str a) deriving Functor

toInt :: N -> Int
toInt Z = 0
toInt (S n) = toInt n + 1
fromInt :: Int -> N
fromInt i = x Z !! i where x s = s : x (S s)

instance Show N where
  show n = show (toInt n)

addN :: N -> N -> N
addN n Z = n
addN n (S m) = S (addN n m)

bs :: (N -> N) -> Str N
-- bs f = Z : [ add t (f Z) | t <- bs (f . S) ]
bs f = Cons Z (fmap (\t -> addN t (f Z)) (bs (f . S)))

{-
Now, let us define it for Church-numbers.
The issue is: types.
-}

type E x = x -> x
type EE x = E (E x)
type EEE x = E (EE x)
type EEEE x = EE (EE x)
type EEEEE x = EE (EEE x)
type F x = x -> E x   -- unused
type C r a = (a -> r) -> r
type C2 a  = C a a
type P r a b  = (a -> b -> r) -> r
type P3 a = P a a a

{- This is as straightforward as I can make it -}
bs_ :: EEE x -> EE (EEE x,EE x) -> EE x
bs_ f n = emit (n cycle init)
          where init = (f,id)
                cycle (f,b) = (f . suc , b `adc` (f zero))
                emit (_,b)  = b 

-- bs_' :: EEE x -> E2 (EEE x,E2 x) -> E2 x
bs_' f n s z
         = emit (n cycle init)  -- use hack to make buffer types the same
           where init buf    = buf f (const id) -- id -- (f,id)
                 cycle buf   = let f = buf (\ x _ -> x)
                                   b = buf (\ _ x -> x)
                               in buf (f . s) ( (b undefined) `adc` (f zero))
                 emit buf    = buf (\ _ b -> b zero) -- (_,b)  = b 


-- zero :: E2 x 
zero = const id
suc :: EEE x 
suc n f = f . n f
adc :: EE x -> EEE x 
adc m n f = m f `mul` n f
mul :: E x -> EE x
mul m n   = n . m
exp m n   = n m
-- one :: E x
one = id
two f = f . f
three f = f . f . f
four = two two
five f = two f . three f
six  = two . three
seven f = three f . four f
eight = three two
nine = two three
ten f =  five f . five f
ff :: [EE x]   -- first few (numbers)
ff = [zero, one, two, three , four, five, six, seven, eight, nine, ten]

sg :: EEE x 
sgbar n s z = n (const z) (s z)
sg    n s z = n (const (s z)) z

pr :: x -> y -> P r x y 
pr x y z = z x y
pi0 :: C a (a -> b -> a) 
pi0 p = p const 
pi1 :: C b (b -> a -> a)
pi1 p = p (\ _ -> id)

thing :: E (P3 a) 
thing p = pr (pi0 p) (pi1 p)

-- squish :: E (E (E (E x))) -> E (E x)
squish h = h suc zero  -- not used ... yet

{- need to play around here -}
sect :: EE a -> EEE a  -- section
sect = const
retr :: EEE a -> EE a  -- retract
retr e3 = e3 zero

{- easy enough -}
-- pair :: (EE x,EEE x) -> EEE x
pair :: (EE x,EEE x) -> EE (EE x) -> EE x
pair (a,f) n s z = n (\ m g _ -> g (f m s z)) zero
                     id (a s z)

fst' :: EEE x -> EE x
fst' f = f zero
snd' :: EEE x -> EEE x
snd' f = f . suc

pair' :: EE x -> EEE x  -> EEEE x -> EE x -- P (EEE x) (EE x) (EEE x)
pair' a f = pair (a,f)
pair'' :: EEEEE x
pair'' n f a = pair (a,f) n 


-- step0 :: E (P (EE x) (EEE x) (EEE x))
-- step0 :: EEE (EEE x)
step0  af = pair' ( (fst' af) `adc` (snd' af zero) ) (snd' af . suc)

{-
start0 :: EE (EEE x)
start0 f = pair' zero f

bs0 :: EEE x -> E (EEE (EEE x)) -> EE x 
bs0 f n = fst' (n step0 start0) suc zero
-}

step :: E (P3 (EEE a)) 
step fa = pr (pi0 fa . suc) (sect ((pi1 fa zero ) `adc` (retr (pi0 fa))))
-- the problem is we are pairing things of different type
-- (Just bodged it so they are the same type.)

step'
  :: (((b1 -> EE x) -> (b1 -> EE x) -> b1 -> EE x) -> b1 -> EE x)
     -> (a -> b1) -> b1 -> P r (a -> EE x) (b2 -> EE x)
step' fa s z =
           let -- pi0fa :: E (E (E x))
               pi0fa = pi0 fa
               -- pi1fa :: E (E (E y))
               pi1fa = pi1 fa
           in pr (pi0fa . s) (const ((pi1fa z ) `adc` (pi0fa z)))
-- step''
--  :: (((b1 -> EE x) -> (b1 -> EE x) -> b1 -> EE x) -> b1 -> EE x)
--     -> (a -> b1) -> b1 -> P r (a -> EE x) (b2 -> EE x)
step'' fa = -- s z =
           let -- pi0fa :: E (E (E x))
               pi0fa = pi0 fa
               -- pi1fa :: E (E (E y))
               pi1fa = pi1 fa
           in pr (pi0fa . suc) ((pi0fa suc (pi1fa suc zero))) -- (pi1fa s (pi0fa s z))  -- (pi1fa `adc` (pi0fa z))

start :: EEE a -> P3 (EEE a) 
start f = pr f (sect zero)

bs' :: EEE a -> EE (P3 (EEE a)) -> EE a
bs' f n = retr (pi1 (n step (start f)))


bp' :: EEE a -> EE (P3 (EEE a)) -> EE a
bp' f n = retr (pi1 (n step (start f)))
          where step fa = pr (pi0 fa . suc)
                          (sect ((pi1 fa zero ) `mul` (retr (pi0 fa))))
                start f = pr f (sect one)

-- doesn't work ... ??
bs'' f n s z = pi1 (n step' (start f) s z) z


wa x = (x . x) `adc` x `adc` x `adc` id -- an (unextended) polynomial
wa_ x = (x . x) `adc` x                 -- [0,2,6,12,20,30,42,56,72,90,110]
wa' x = wa x . suc x  -- another
wa'' = wa . sgbar

test_bs' f = map (\n -> see_num (bs' f n)) ff
test_bs_ f = map (\n -> see_num (bs_ f n)) ff
test_bp' f = map (\n -> see_num (bp' f n)) ff
-- see_fun :: EEE Int -> [Int]
see_fun f      = map (see_num . f) ff
see_num :: EE Int -> Int
see_num n = n (+1) 0

{-

                   (\ n s z -> n (const (s z)) z)
                =  (\ n s z -> (n . const . s) z z)
                =  (\ n s -> diag (n . const . s))
This function is the same as sg : it is 011111...

applying bounded sums to sg, one gets the predecessor: 
λ> let diag f x = f x x ; a =  (\ n s -> diag (n . const . s)) in test_bs' a
[0,0,1,2,3,4,5,6,7,8,9]

factorial
λ> test_bp' suc
[1,1,2,6,24,120,720,5040,40320,362880,3628800]

λ> see_fun (\n -> (n `mul` n) `adc` n)
[0,2,6,12,20,30,42,56,72,90,110]

λ> map (see_num . bs0 (\n -> (n `mul` n) `adc` n)) tdom
[1,3,7,13,21,31,43,57,73,91,111]

λ>  [ see_num (bs0 (\n -> (n `mul` n) `adc` n) x) | x <- tdom]
[1,3,7,13,21,31,43,57,73,91,111]


-}




