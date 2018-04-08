module _ where

{- Investigation of Zero and One types in type-theory.
   Once one has setup Zero, one automatically has a
   "pale imitation" of N_1, Per's standard, inductive data-singleton.

   The general question is: what is this pale imitation
   good for? How does it differ from the inductive singleton?
-}

-- could use terms "magic" for efq, and "MAGIC" for EFQ.

-- normal Id stuff.
  data Id_ (A : Set) (a : A) : A -> Set where
    refl : (Id A) a a

  IdElim : {A : Set}-> (a : A) ->
           (C : A -> Set)->
           (c : C a)->
           (a' : A)->
           (â : (Id A) a a' )-> C a'
  IdElim a C ca .a refl = ca

-- normal-ish empty data-type.
  data O : Set where

  EFQ : O -> Set   -- define the empty family of sets
  EFQ ()           -- by empty cases

  efq : (C : O -> Set)-> (x : O)-> C x
  efq a () 

-- pale imitation of 1

  Sole : Set
  Sole = (x : O)-> EFQ x

  EqSole : Sole -> Sole -> Set
  EqSole s s' = (x : O)-> (Id EFQ x) (s x) (s' x)

  question2 : (s s' : Sole)-> EqSole s s'
  question2 s s' = efq λ x → (Id EFQ x) (s x) (s' x) 

  sole : Sole         -- the "solitary" inhabitant of Sole.
  sole = efq EFQ

  question2' : (s : Sole)-> EqSole s sole
  question2' s = efq λ x → (Id EFQ x) (s x) (sole x) 


  -- can we interpret the "strong" elimination rule of Per's N_1,
  -- with our "pale imitations"?
  question1 : (C : Sole -> Set)->
             C sole -> (x : Sole)-> C x
  question1 C x₁ x = {!!}   -- probably not

  -- can we prove that any two inhabitants of Sole are identical?
  question1' : (s : Sole)-> (Id Sole) s sole
  question1' s = {!refl!}
  
{- It seems one can prove that any two elements
of Sole are extensionally equal, and in particular that any element
is extensionally equal to our favourite one. 
But not that our two elements are identical as inhabitants
of a function type. 
-}
    
