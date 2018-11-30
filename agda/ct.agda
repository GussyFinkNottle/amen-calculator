module _ (A : Set) where

{- 
Exploration of 3 topics:
1. continuation monad
2. peirce monad
3. classical principles, and whether they require efq

The parameter is a completely generic "bottom" type A.
So there is no efq axiom

   efq : { x : Set }-> A -> x

or its dependent version. 
We wish to see how the classical principles inter-relate
in the absence of efq.
-}

  -- a few essential combinators.
  -- There should be one copy of this somewhere.

module mycombinators where
  infixr 3 _∘_
  _∘_ :  -- composition B
      {X : Set} {Y : X -> Set} {Z : (x : X)-> Y x -> Set} ->
      (f : {x : X}-> (y : Y x) -> Z x y) ->  
      (g : (x : X)-> Y x) ->
           (x : X) -> Z x (g x)
  (f ∘ g) x = f (g x)
  _∘'_ :  -- composition. More restrained type.
      {X : Set} {Y : Set} {Z : Y -> Set} ->
      (f : (y : Y) -> Z y) ->  
      (g : (X -> Y)) ->
           (x : X) -> Z (g x)
  (f ∘' g) x = f (g x)

  infixr 4 _^_
  _^_ [^] : -- exponentiation E 
        {X : Set}->{Y : X -> Set}->
        (x : X) -> ((x' : X) -> Y x') -> Y x
  (a ^ f) = f a
  [^]     = _^_ 

  _~_ : -- flip/converse C
       {X : Set}->{Y : Set}-> {Z : X -> Y -> Set}->
       ((x : X) -> (y : Y) -> Z x y) ->
       ((y : Y) -> (x : X) -> Z x y) 
  (f ~ a) x = f x a

  diag : -- W combinator
         {X : Set}-> {Y : X -> X -> Set }->
         ((x : X) -> (x' : X) -> Y x x') ->
         (x : X)-> Y x x 
  diag f x = f x x

  const : -- K combinator
         {X : Set}-> {Y : X -> Set }->
         (x : X) -> Y x -> X
  const a _ = a

  id : -- I combinator
       {X : Set}-> X -> X
  id a = a

  zero : {X : Set}-> {Y : X -> Set}->  (x : X) → Y x -> Y x
  zero _ = id 
--   zero {X} {Y} x = id {Y x}  

  -- some notational madness
  
  _<- : Set -> Set -> Set
  _<- X Y = Y -> X

  -- continuations/double-negation monad

  C : Set -> Set
  C X = (A <-) ((A <-) X)

  map :   {X : Set}-> {Y : Set} ->
          (X -> Y) -> C X -> C Y
  map m cta k =  cta ((_∘_ ~ m) k)
  -- cta (k ∘ m) 

  ret : -- this is really the exponentiation combinator
         {X : Set}->     X -> C X
  ret      = _^_ -- x k = k x

  join : -- this is really (_^_) ^ ((_~_) (_∘_) )
         {X : Set}->  C (C X) -> C X
  join cc  =  cc ∘ ret

  bind : -- just follow the formula
         {X : Set}-> {Y : Set}->
            C X -> (X -> C Y) -> C Y
  bind {X} {Y} m c 
             = join (map c m) 


-- peirce monad

  pF : Set -> Set
  pF a = ((a -> A) -> a)

  pm :   {x : Set}-> {y : Set} ->
          (x -> y) -> pF x -> pF y
  pm x2y x y  = (x2y ∘ x) (y ∘ x2y) 

  pr :   {x : Set}-> x -> pF x
  pr         = const -- λ x _ → x

  pj :   {x : Set}-> 
         pF (pF x) -> pF x
  pj ppx k   = ppx (λ x → k (x k)) k 

  pb :  {X : Set}-> {Y : Set}-> pF X -> (X -> pF Y) -> pF Y
  pb m c     = pj (pm c m)

  pA : Set -> Set     -- the form of Peirce's law: an algebra for the pF monad.
  pA a       = pF a -> a 

   -- C-kleisli-ish forms of Peirce's law.
   
  thingC : { X : Set }-> {b : Set}->
          ((X -> A) -> C X) -> C X
  thingC = diag     -- x k  =   diag x k

{-
  thingP : { a : Set }-> {b : Set}->
          ((a -> pF b) -> pF a) -> pF a
  thingP {A} {B} x   =  x λ a b2A → {!!}  

-}

  data _⊕_ (A : Set) (B : Set) : Set where
    inL : A -> A ⊕ B
    inR : B -> A ⊕ B

  record _⊗_ (A : Set) (B : Set) : Set where
       constructor <_,_>
       field
         fst : A 
         snd : B
  open _⊗_ public 

  lemma :  {A : Set} -> {B : Set} -> {C : Set} ->
           (A -> C) -> (B -> C) -> ((A ⊕ B) -> C)
  lemma {A} {B} {C} a2c b2c = f
        where f :  (A ⊕ B) -> C
              f (inL x) = a2c x
              f (inR x) = b2c x
  lemma'' :  {A : Set} -> {B : Set} -> {C : Set} ->
           (A -> C) ⊗ (B -> C) -> ((A ⊕ B) -> C)
  lemma'' a2cb2c = lemma (fst a2cb2c) (snd a2cb2c)

  lemma'  :  (A : Set) -> (B : Set) -> (C : Set) ->
            (A ⊕ B -> C) -> (A -> C) ⊗ (B -> C)
  lemma' A B C
         aub2c = < aub2c ∘ inL , aub2c ∘ inR >


  module _  (pp : (a : Set) -> ((a -> A)-> a) -> a) where
  -- What do we get if we have an algebra for the Peirce monad?
  -- depending on the carrier, (which must have the form
  -- a ⊕ (a -> A) ), we can be sure the carrier is non-empty.
  -- So as schemas, Peirce subsumes EM. 
  
    not : Set -> Set
    not p = p -> A

    remark : (P : Set)-> (not P -> P) -> P
    remark = pp 

    em stable : Set -> Set
    em P = P ⊕ (not P)

    thm : -- excluded middle
          (P : Set) -> em P
    thm P = let    body : not (em P) -> em P
                   body em2r = inR (em2r ∘ inL) 
            in pp (em P) body 

    notnot  : Set -> Set
    notnot p = not (not p)   -- need large composition

    thm' : -- this is provable without pp
           (P : Set) -> notnot (em P)
{-    thm' P =   (λ y → snd y (fst y)) ∘ (lemma' P (not P) A)  -}
    thm' P =   let b   : not (P ⊕ not P) → (not P ⊗ notnot P)
                   b   = lemma' P (not P) A
                   a   : not (not P ⊗ notnot P) 
                   a y = snd y (fst y)
               in a ∘ b

    stable P = notnot P -> P  -- probably needs efq, not just pp

    -- however, it is OK on negative instances
    -- doesn't need pp
    lemmy_the_lemma : (P : Set)-> stable (not P)
    lemmy_the_lemma P not₃p  = not₃p ∘ ret 


{-
    thm'' : (P : Set)-> notnot P -> P  -- probably requires efq
    thm'' P nnp =
       let t1 : P 
           t1 = pp P {!!}  λ x → {!!}
           t2 : dn P
           t2 = pp (dn P) A {!!}
       in {!!}
-}

    
  
