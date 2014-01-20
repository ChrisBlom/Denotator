{-# LANGUAGE DeriveDataTypeable #-}
{-- The Frame module provide the basic datatypes used in semantics.
 	These are entities	
 -}
module Frame where

import Data.Typeable
import Data.List
 
{- In Frame.hs we set up our universe of discourse.
   All we have to do is give the atomic domains (of entities and truthvalues),
   Haskell will then do all the lambda abstraction and function application stuff-}

{- E : the datatype used to represent Entities.
       Entities are a finite collection (hence instance of Enum and Bounded) -}
data E = Yoda | Luke | Leia | Han | Vader | Chewbacca
  deriving (Eq,Show,Enum,Bounded,Typeable)

{- T : a type synonym for Bool.
   Bool is Haskell's built-in type for truth-values.
   (It is defined as: data Bool = True | False )
  -}
type T = Bool

{- entities : a list of all entities in the frame -}
entities :: [E]
entities = [minBound..maxBound]

{- truthvalues : a list of all truthvalues in the frame -}
truthvalues :: [T]
truthvalues = [True,False]
