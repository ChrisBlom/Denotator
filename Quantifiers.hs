module Quantifiers where

import Frame
import FrameUtils
import Boolean

everyone :: (E->T) -> T
everyone f = forall f

someone :: (E->T) -> T
someone f = exists f

every :: (E->T) -> (E->T) -> T
every f g = f .<. g

some :: (E->T) -> (E->T) -> T
some f g = exists (f /\ g)

no :: (E->T) -> (E->T) -> T
no f g = complement exists (f /\ g) 

no_one :: (E->T) -> T
no_one f = no one f

