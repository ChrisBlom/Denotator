module Quantifiers where

import Frame
import FrameUtils

-- Quantifiers
exists,forall :: (FrameType a) => ( a -> T ) -> T
exists f  = any f (domain f)
forall f  = all f (domain f)