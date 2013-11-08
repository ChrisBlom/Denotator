{-# LANGUAGE TypeSynonymInstances #-}
module Boolean where

import Frame
import FrameUtils
import Quantifiers

{---- Boolean Type Class --------------------------------}

-- Boolean type class defines common operation for 
-- functions which are characteristic functions of set/relations -}
class (FrameType a) => Boolean a where
  (/\)  :: a -> a -> a -- and
  (\/)  :: a -> a -> a -- or
  complement :: a -> a      -- not
  (.<.) :: a -> a -> T -- numerical order
  one   :: a           -- top
  zero  :: a           -- bottom

infix 8 /\
infix 8 \/

-- T is a Boolean type
instance Boolean T where
  x /\ y   = x && y
  x \/ y   = x || y
  complement x  = not x
  x .<. y  = x ==> y
  one      = True
  zero     = False

-- if type b is Boolean then (a->b) is Boolean as well
instance (FrameType a,Boolean b) => Boolean (a -> b) where
  f /\ g   = \x -> f x /\ g x
  f \/ g   = \x -> f x \/ g x
  complement f  = \x -> complement (f x)
  f .<. g  = forall ( \x -> f x .<. g x )
  one      = \x -> one
  zero     = \x -> zero