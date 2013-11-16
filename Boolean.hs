{-# LANGUAGE TypeSynonymInstances, ScopedTypeVariables #-}
module Boolean where

import Frame hiding ( (==>))
import FrameUtils

import Test.QuickCheck

-- Boolean type class defines common operation for T or Boolean functions
-- (characteristic functions of set/relations) 
-- -}
class (FrameType a) => Boolean a where
  (/\)  :: a -> a -> a -- join
  (\/)  :: a -> a -> a -- meet
  complement :: a -> a -- complement
  (.<.) :: a -> a -> T -- order
  (.=.) :: a -> a -> T -- order
  one   :: a           -- top
  zero  :: a           -- bottom

infix 8 /\
infix 8 \/

-- T is a Boolean type
instance Boolean T where
  x /\ y        = x && y
  x \/ y        = x || y
  complement x  = not x
  x .<. y       = x < y
  one           = True
  zero          = False
  a .=. b       = a == b

-- if type b is Boolean then (a->b) is Boolean as well
instance (FrameType a,Boolean b) => Boolean (a -> b) where
  f /\ g        = \x -> f x /\ g x
  f \/ g        = \x -> f x \/ g x
  complement f  = complement . f
  f .<. g       = forall ( \x -> f x .<. g x )
  f .=. g       = forall ( \x -> f x .=. g x )
  one           = \_ -> one
  zero          = \_ -> zero

onex :: (E->T)
onex = one
zerox :: (E->T)
zerox = zero


instance Arbitrary E where
  arbitrary = elements [minBound..maxBound]
instance CoArbitrary E where
  coarbitrary = variant . fromEnum

entails f g = ( f .<. g ) 
is_restrictive m   = (\ f ->   m f .<. f )
is_corestrictive m = (\ f ->   m f .<. complement f )
is_disjoint f g    = (  \x ->  (f /\ g) x .=. zero  )
is_intersectiveWith m f = (\g -> (m g) .=. (f /\ g)  )


fake :: (E->T) -> (E-> T)
fake x = complement x     






