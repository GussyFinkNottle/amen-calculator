module Hankombinatory where

{-
I make heavy use of general combinators,
both the `classical' SKI, BCIKW, and the
`neo-classical' AMEN. 

Very often, combinators are `binary', and
can benefit from infix notation. 
Sometimes, they are unary, and can benefit from postfix notation.

The notation is experimental, but some parts are like conventional
|∘| are very solid. 
-}

  infixl 3 _∘_
  _∘_ _↑∘  :  -- composition B
      {X : Set} {Y : Set} {Z : Y -> Set} ->
      ((y : Y) -> Z y) ->
      (g : X -> Y) ->
      (x : X) -> Z (g x)
  (f ∘ g) x = f (g x)
  [∘] = (_∘_)
  (a ↑∘)  = _∘_ a

  infixr 3 _×_
  _×_ _↑× :  -- flip of composition
      {X : Set} {Y : Set} {Z : Y -> Set} ->
      (f : X -> Y) ->
      (g : (y : Y) -> Z y) ->
      (x : X) -> Z (f x)
  (f × g) x = g (f x)
  [×] = (_×_)
  (a ↑×)  = _×_ a

  infixr 4 _^_
  _^_ _↑^ : -- exponentiation E 
        {X : Set}->{Y : X -> Set}->
        (x : X) -> ((x' : X) -> Y x') -> Y x
  (a ^ f) = f a 
  [^] = (_^_)
  (a ↑^)  = _^_ a

  _~_ _↑~ : -- flip/converse C
       {X : Set}->{Y : Set}-> {Z : X -> Y -> Set}->
       ((x : X) -> (y : Y) -> Z x y) ->
       ((y : Y) -> (x : X) -> Z x y) 
  (f ~ a) x = f x a
  [~] = (_~_)
  (a ↑~)  = _~_ a

  diag : -- W combinator
         {X : Set}-> {Y : X -> X -> Set }->
         ((x : X) -> (x' : X) -> Y x x') ->
         (x : X)-> Y x x 
  diag f x = f x x

  const _↑K : -- K combinator
         {X : Set}-> {Y : X -> Set }->
         (x : X) -> Y x -> X
  const a _ = a
  _↑K {X} {Y}    = const 

  -- unary combinators
  id _↑1 : -- I combinator
       {X : Set}-> X -> X
  id a = a
  _↑1  = id
  
  zero  _↑0 : {X : Set}-> {Y : X -> Set}->  (x : X) → Y x -> Y x
--   zero {X} {Y} x  = id {Y x}
  zero _  = id
  _↑0     = zero 

  -- S combinator.  Maybe I prefer _▷_ 
  _ˢ_ _▷_ _↑▷ :
        {A : Set}->
        {B : A -> Set}->
        {C : (x : A)-> B x -> Set}->
        (f : (x' : A) → (y' : B x')-> C x' y' )-> 
        (g : (x' : A) -> B x' )-> 
        (x : A) -> C x (g x)
  (f ˢ g) x = f x (g x)
  _▷_       =  _ˢ_
  _↑▷       =  _▷_

  -- I like having this converse of the S combinator.
  _◁_   : {A : Set}->
          {B : A -> Set}->
          {C : (x : A)-> B x -> Set}->
          (g : (x' : A) -> B x') -> 
          (f : (x' : A) → (y' : B x') → C x' y') →
          (x : A) → C x (g x)
  _◁_   = _~_ _▷_ 

  -- Addition
  _+_  _↑+ : { A : Set}->
        { B : A -> Set}->
        { C : A -> Set}->
        { D : (x : A) -> C x -> Set }->
         (f : ( x  : A) -> (y : B x) -> C x ) -> 
         (g : ( x' : A) -> (c : C x')  -> D x' c) ->
         (a'' : A) -> (b'' : B a'') -> D a'' ((a'' ^ f) b'')
  (f + g) x = (x ^ f) × (x ^ g)
  _↑+ f g   = f + g
  [+]       = _+_ 
