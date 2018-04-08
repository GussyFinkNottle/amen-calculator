module _ where
{-
   Investigation of Zero and One types in type-theory.
   Once one has setup Zero, one automatically has a
   "pale imitation" of N_1, Per's standard, inductive data-singleton.

   The general question is: what is this pale imitation
   good for? How does it differ from the inductive singleton?
-}

-- could use terms "magic" for efq, and "MAGIC" for EFQ.

-- normal Id stuff.
  data Id_ (A : Set) (a : A) : A -> Set where
    refl : (Id A) a a

  IdElim : {A : Set}-> (a : A) ->    -- strong, a la Christine
           (C : ( x : A) -> (Id A) a x -> Set)->
           (c : C a refl)->
           (a' : A)-> (â : (Id A) a a' )-> C a' â
  IdElim a C ca .a refl = ca

-- normal-ish empty data-type.
  data O : Set where

  EFQ : O -> Set   -- define the empty family of sets
  EFQ ()           -- by empty cases

  efq : (C : O -> Set)-> (x : O)-> C x
  efq a () 

  data O' : Set where  S : O' -> O'
  EFQ' : O' -> Set
  EFQ' (S z) = EFQ' z

  efq' : (C : O' -> Set)->
         (( x : O') -> C x -> C (S x))->
         (x : O')-> C x
  efq' C cs (S z) = cs z (efq' C cs z) -- efq' C {!z!} {!!}  -- {!z!} -- a () 

  efq'' : (C : O' -> Set)->
          O' -> (x : O')-> C x
  efq'' C = efq' (λ _ → (x : O')-> C x)  λ _ x₁ → x₁

  
-- pale imitation of 1

  I : Set
  I = (x : O)-> EFQ x

  ExtI : I -> I -> Set   -- extensional equality of empty functions.
  ExtI s s' = (x : O)-> (Id EFQ x) (s x) (s' x)

  question2 : (s s' : I)-> ExtI s s'  -- yes, they're all extensionally equal.
  question2 s s' = efq λ x → (Id EFQ x) (s x) (s' x) 

  sole : I         -- our favourite inhabitant of I.
  sole = efq EFQ   -- it exists because of EFQ.

  question2' : (s : I)-> ExtI s sole  -- hardly worth saying
  question2' s = question2 s sole 

  {- Per's N₁.  Is it any bloody use? -} 
  data N₁ : Set where ô : N₁
  N₁_Elim  :    (C : N₁ -> Set)-> C ô -> (x : N₁)-> C x
  N₁ C Elim c₁ ô = c₁                

  -- can we interpret the "strong" elimination rule of Per's N_1,
  -- with our "pale imitations"?
  question1 :   (C : I -> Set)->
                C sole -> (x : I)-> C x
  question1 C x₁ x = {!x₁!}   -- probably not.

  -- can we prove that any two inhabitants of I are identical?
  question1'   : (s : I)-> (Id I) s sole
  question1' s = {!refl!}    -- this could be bad. Luo & Healf?
  
{- 
It seems one can prove that any two elements
of I are extensionally equal, and in particular that any element
is extensionally equal to our favourite one. 
But not that all elements of this function type are identical.
-}
    
  module _ where

-- the question arises, what if there are constructors for O, but no constants.
-- The role played by diagonalisation here is genuinely mysterious to me. 
-- Thanks to Pierre-Evariste Dagand. 

  data O'' : Set where 
    S : O'' -> O''

  Etry : O'' -> Set
  Etry (S z) = Etry z 

  module EFQ' (E : O'' -> Set) where

    g : O'' → (x : O'') → E x
    g (S y) x = g y x

    g' : O'' → (x : O'') → E x  
    g' (S y) = g' y

    elim : (x : O'')-> E x
    elim x = g x x        -- NB diagonalising

    elim' : (x : O'')-> E x
    elim' x = g' x x


