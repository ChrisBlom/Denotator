{-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, TypeFamilies #-}

module Syntax where

{- In the Syntax module the syntactic types are defined, as well
   as ways to store these in a uniform container -}

import Frame
import FrameUtils

{- Type level syntactic types -}
data NP = NP          deriving (Eq,Show)
data S  = S           deriving (Eq,Show)
data N  = N           deriving (Eq,Show)
data NUM = NUM        deriving (Eq,Show)
data a :\ b = a :\ b  deriving (Eq,Show)
data a :/ b = a :/ b  deriving (Eq,Show)
data a :* b = a :* b  deriving (Eq,Show)

infixr 5 :\
infixl 6 :/

-- The CorrespondingTypes type class defines the relation beteen
-- syntactic and semantic types.
class (SyntacticType a,FrameType b) => CorrespondingTypes a b where
instance CorrespondingTypes NP   E
instance CorrespondingTypes N   (E->T)
instance CorrespondingTypes S   (T)
instance CorrespondingTypes NUM (Integer)
instance (CorrespondingTypes a a'
         , CorrespondingTypes b b')
         => CorrespondingTypes (a :\ b)  (a' -> b')
instance (CorrespondingTypes a a'
         , CorrespondingTypes b b')
         => CorrespondingTypes (b :/ a)  (a' -> b')
instance ( CorrespondingTypes a a'
         , CorrespondingTypes b b')
          => CorrespondingTypes (a :* b) (a', b')


{- SynCat : Syntactic Categories, uniform wrapper for syntactic types -}
data SynCat
  = WNP
  | WN
  | WS
  | WNum
  | SynCat :/: SynCat
  | SynCat :\: SynCat
  | SynCat :*: SynCat
  | WList [SynCat]  
  deriving Eq

-- The SyntacticType type-class defines which types are syntactic
-- types, and provides means to put these into a uniform container
class SyntacticType a where
  wrap :: a -> SynCat
instance SyntacticType NP   where wrap NP = WNP
instance SyntacticType N    where wrap N = WN
instance SyntacticType NUM  where wrap NUM = WNum
instance SyntacticType S    where wrap S = WS
instance (SyntacticType a,SyntacticType b) => SyntacticType (a :\ b)  where
  wrap (a:\b) = (wrap a) :\: (wrap b)
instance (SyntacticType a, SyntacticType b) => SyntacticType (b :/ a)  where
  wrap (b:/a) = (wrap b) :/:  (wrap a)
instance (SyntacticType a , SyntacticType b) => SyntacticType (a :* b)   where
  wrap (a:*b) =  (wrap a) :*: (wrap b)
instance (SyntacticType a) => SyntacticType [a]   where
  wrap a = WList $ map wrap a

-- Show instanc for SynCat
instance Show SynCat where
  showsPrec d x = case x of
    WNP      -> showString "np"
    WNum     -> showString "num"
    WN       -> showString "n"
    WS       -> showString "s"
    WList x  -> showsPrec (0) x
  --  (a :\: b :/: c) | a == b && b == c -> showString  ">" . showsPrec (10+1) b . showString "<"

    (a :\: b) ->
          showParen (d > up_prec) $
             showsPrec (up_prec+1) a . showString "\\" .  showsPrec (up_prec+1) b
             where up_prec = 10
    (a :*: b) ->
          showParen (d > up_prec) $
             showsPrec (up_prec+1) a . showString "*" .  showsPrec (up_prec+1) b
             where up_prec = 10
    (a :/: b) ->
          showParen (d > up_prec) $
             showsPrec (up_prec+1) a . showString "/" .  showsPrec (up_prec+1) b
             where up_prec = 10



brackets x = "["++x++"]"
parens a = "("++a++")"
bracket a = "("++a++")"
cbracket a = "{"++a++"}"
sbracket a = "["++a++"]"
dbracket a = "[|"++a++"|]"