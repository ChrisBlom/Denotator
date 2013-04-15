{-# LANGUAGE DeriveDataTypeable, TypeFamilies, FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving #-}
{- FrameUtils.hs - ( chris.blom@phil.uu.nl ) -}
module FrameUtils where

{-    You do not have to edit anything in this file.

   In FrameUtils functionality some extra functionality for
   types defined in Frame.hs is defined.

   For each function/value in our frame we can get the
   - domain
   - codomain
   - functionSpace it is in
   - pretty printing functions

   Additionally, casting to Data.Dynamic for frame types is defined here.
-}

import Frame
import Data.Dynamic
import Data.Typeable

import Data.Maybe
import Data.List
import Data.Char

-- Logical implication
(==>) :: T -> T -> T
True ==> False = False
_    ==> _     = True


-- Cartesian product
cartesian a b = [ (x,y) | x <- a , y <- b ]

{- S : Worlds, a wrapper around Int, Haskells built in type for integers. -}
newtype W = World Int
  deriving (Eq,Ord,Enum,Typeable)

instance Show W where show (World x) = show x

newtype Z = Time Int deriving (Eq,Ord, Enum,Show,Typeable)

{- worlds : a list of all the worlds in the frame -}
worlds :: [W]
worlds = [(World 1)..(World 3)]

{- timepoints : a list of all the timepoints in the frame -}
times :: [Z]
times = [ (Time 0)..(Time 1000)]



{-- FrameType defines which types are used in the frame,
    and provides extra functionality for those types.  -}
class ( Eq f,Typeable f) => FrameType f  where
  type DomainType f
  type TargetType f
  data FTree      f
  domainElem        :: f -> (DomainType f)
  targetElem        :: f -> (TargetType f)
  functionSpaceOf   :: f -> [f]                   -- exponential object
  domain            :: f -> [DomainType f]        -- source object
  target            :: f -> [TargetType f]        -- target object
  image             :: f -> [TargetType f]
  showI             :: f -> String
  treeI             :: f -> (FTree f )
  hide              :: (Typeable f) => f ->  Denotation
  uncover           :: Denotation -> Maybe f
  hide              = Sem . toDyn
  uncover  (Sem x)  = fromDynamic x
  domainElem f = head (domain f)
  targetElem f = head (target f)




instance FrameType E  where
  data FTree E  = LeafE E
  type DomainType E = E
  type TargetType E = E
  domain _        = entities
  target _        = entities
  functionSpaceOf _ = entities
  image _         = entities
  treeI           = LeafE
  showI = show
  
instance FrameType Integer  where
  data FTree Integer  = LeafInt Integer
  type DomainType Integer = Integer
  type TargetType Integer = Integer
  domain _        = [0..]
  target _        = [0..]
  functionSpaceOf _ = [0..]
  image _         = [0..]
  treeI           = LeafInt
  showI = show


instance FrameType T where
  data FTree T  = LeafT T
  type DomainType T = T
  type TargetType T = T
  domain _        = truthvalues
  target _        = truthvalues
  functionSpaceOf _ = truthvalues
  image _         = truthvalues
  treeI           = LeafT
  showI = show

instance FrameType W where
  data FTree W   = LeafW W
  type DomainType W = W
  type TargetType W = W
  domain _        = worlds
  target _      = worlds
  functionSpaceOf _ = worlds
  image _         = worlds
  treeI           = LeafW
  showI = show

instance FrameType Z where
  data FTree Z  = LeafZ Z
  type DomainType Z = Z
  type TargetType Z = Z
  domain _        = times
  target _      = times
  functionSpaceOf _ = times
  image _         = times
  treeI           = LeafZ
  showI = show

instance (FrameType a ,FrameType b ) => FrameType (a->b) where
  type DomainType (a->b) = a
  type TargetType (a->b) = b
  data FTree (a->b) = FSplit [(a , FTree b)]
  domain f          = functionSpaceOf (domainElem f)
  target f          = functionSpaceOf (targetElem f)
  image f           = nub $ map f (functionSpaceOf (domainElem f))
  functionSpaceOf f = functionSpace (domain f) (target f)
  showI f = concatMap (\x -> ( (showI x) ++ "|->" ++ (showI ( f x )) ++ "\n"  )) (domain f)
  treeI f = FSplit [ (x,treeI $ f x) | x <- (domain f) ]

instance (FrameType a ,FrameType b ) => FrameType (a,b) where
  type DomainType (a,b) = (a, b)
  type TargetType (a,b) = (a,b)
  data FTree (a,b) = FPair (FTree a , FTree b)
  domain (a,b)      = cartesian (functionSpaceOf a) (functionSpaceOf b)
  target (a,b)      = cartesian (functionSpaceOf a) (functionSpaceOf b)
  image  (a,b)      = cartesian (functionSpaceOf a) (functionSpaceOf b)
  functionSpaceOf  (a,b)      = cartesian (functionSpaceOf a) (functionSpaceOf b)
  showI (a,b) = concat [ "(" ,  showI a, showI b,  ")" ]
  treeI (a,b) = FPair (treeI a, treeI b)

instance (FrameType a ,FrameType b , FrameType c ) => FrameType (a,b,c) where
  type DomainType (a,b,c) = (a,b,c)
  type TargetType (a,b,c) = (a,b,c)
  data FTree (a,b,c) = FThree (FTree a , FTree b,FTree c)
  domain (a,b,c)      = [ (x,y,z) | x <- (functionSpaceOf a) , y <- (functionSpaceOf b) , z <- (functionSpaceOf c) ]
  target (a,b,c)      = [ (x,y,z) | x <- (functionSpaceOf a) , y <- (functionSpaceOf b) , z <- (functionSpaceOf c) ]
  image  (a,b,c)      = [ (x,y,z) | x <- (functionSpaceOf a) , y <- (functionSpaceOf b) , z <- (functionSpaceOf c) ]
  functionSpaceOf  (a,b,c)      = [ (x,y,z) | x <- (functionSpaceOf a) , y <- (functionSpaceOf b) , z <- (functionSpaceOf c) ]
  showI (a,b,c) = concat [ "(" ,  showI a, showI b,showI c,  ")" ]
  treeI (a,b,c) = FThree (treeI a, treeI b,treeI c)

instance (FrameType a,FrameType b) => Eq (a -> b) where
  f == g = all (\x -> (f x == g x) ) (domain f)

spacer n = take 5 $ repeat ' '
instance Show (FTree E) where showsPrec p (LeafE x) i = i++spacer p ++ show x ++ "\n"
instance Show (FTree T) where showsPrec p (LeafT x) i = i++spacer p ++ show x ++ "\n"
instance Show (FTree W) where showsPrec p (LeafW x) i = i++spacer p ++ show x ++ "\n"
instance Show (FTree Z) where showsPrec p (LeafZ x) i =i++ spacer p ++ show x ++ "\n"
instance (Show (FTree b),Show a) => Show (FTree (a->b) ) where
  showsPrec n (FSplit x) i =
    concat $
      [ concat [ showsPrec (n+10) a i' , " |-> ",  showsPrec (0) b "\n" ] | (a,b) <- x ]  where  i' = spacer n



relation_to_function :: (Eq a) =>  [(a,b)] -> a -> b
relation_to_function [] _ = undefined
relation_to_function ((l,r):t) x
  | l == x 	= r
  | otherwise = relation_to_function t x

functionSpace :: (Eq a) => [a] -> [b] -> [a->b]
functionSpace a b = do
  funcrel <- sequence $ map (\ae -> [ (ae,be) | be <- b] ) a
  return ( relation_to_function funcrel)


-- class (Typeable a) => SemanticType a where





newtype Denotation = Sem Dynamic



typeE = typeOf (undefined::E)
typeT = typeOf (undefined::T)
typeTT = typeOf (undefined::(T -> T))
typeET = typeOf (undefined::(E->T))
typeEET = typeOf (undefined::(E->E->T))
typeETT = typeOf (undefined::((E->T)->T))
typeETET = typeOf (undefined::((E->T)->E -> T))
typeTTT = typeOf (undefined::(T -> T -> T))
typeListE = typeOf ([undefined::E])


showType (Sem x) = reverse $ clean [] $ concat [show (dynTypeRep x)  ] where
      clean cleaned []= cleaned
      clean cleaned (' ':t) = clean cleaned t
      clean cleaned ('F':'r':'a':'m':'e':'.':t) = clean cleaned t
      clean cleaned ('B':'o':'o':'l':t) = clean ('T' : cleaned) t
      clean cleaned ('-':'>':t) = clean cleaned t
      clean cleaned (h:t) = clean (h : cleaned) t

      typeRep = dynTypeRep x
      showcast t
          | t == typeE   = show $fromJust $  ((fromDynamic x) :: Maybe (E))
          | t == typeT   = show $fromJust $ ((fromDynamic x) :: Maybe (T))
          | t == typeET  = show $ fromJust$ ((fromDynamic x) :: Maybe (E -> T))
          | t == typeEET = show $fromJust $  ((fromDynamic x) :: Maybe (E -> E -> T))
          | t == typeETT  = show $fromJust$  ((fromDynamic x) :: Maybe ((E->T)->T))
          | t == typeListE  = show $fromJust$  ((fromDynamic x) :: Maybe ([E]))
          | otherwise = "~"

isId f = all (\x -> (f x) == x ) (domain f)



instance Show Denotation where
  show (Sem x) = reverse $ clean [] $ concat [ "" , showcast typeRep ] where
      clean cleaned []= cleaned
      clean cleaned ('F':'r':'a':'m':'e':'.':t) = clean cleaned t
      clean cleaned ('B':'o':'o':'l':t) = clean ('T' : cleaned) t
      clean cleaned (h:t) = clean (h : cleaned) t

      typeRep = dynTypeRep x
      showcast t
          | t == typeE   = show $fromJust $  ((fromDynamic x) :: Maybe (E))
          | t == typeT   = show $fromJust $ ((fromDynamic x) :: Maybe (T))
          | t == typeTT   = show $fromJust $ ((fromDynamic x) :: Maybe (T -> T))
          | t == typeET  = showFunctionAsSet $fromJust$ ((fromDynamic x) :: Maybe (E -> T))
          | t == typeEET = show $ fromJust$  ((fromDynamic x) :: Maybe (E -> E -> T))
          | t == typeETET = show $ fromJust$  ((fromDynamic x) :: Maybe ((E -> T) -> E -> T))
      --    | t == typeETT  = bla $fromJust$  ((fromDynamic x) :: Maybe ((E->T)->T))
          | t == typeListE  = show $fromJust$  ((fromDynamic x) :: Maybe ([E]))
          | otherwise =  "~"

showFunctionAsSet f = showAsSet $ filter f (domain f)
showAsSet x = (\x -> "{"++x++"}") $ concat $intersperse "," $  map show x
showAsSetAbbr x = (\x -> "{"++x++"}") $ concat $intersperse "," $  map (take 2 . show) x
asSet2 x = (\x -> "{"++x++"}\n") $ concat $ intersperse "," x

bla f = asSet2 $ map asSet2 $ (map.map) (take 2 . show) ents
  where
    sets = filter f (domain f)
    ents = map (\x -> filter x (domain x)  ) sets

bla2 f =  asSet2 $ map (\(a,b) -> concat ["(",showAsSetAbbr a," , ",showAsSetAbbr b,")\n"] ) ents
  where
    sets = filter (uncurry f) (cartesian (domain f) (domain f))
    ents = map (\(x,y) -> (filter x (domain x),filter y (domain y))  ) sets

instance Show (W->E) where
  show f = show $ map (\x -> (x , f x) ) (domain f)
instance Show (E->T) where
  show f = showAsSet $ filter f (domain f)
instance Show (T->T) where
  show f = showAsSet $ filter f (domain f)

instance Show ((E->T)-> E ->T) where
  show f
    | isId f    = "'identity function'"
    | otherwise = "~" -- show $ map (\x -> concat $ [show x,"|->",show $ f x]) (domain f)
instance Show (W->T) where
  show f = showAsSet $ filter f (domain f)

instance Show (E->E->T) where
  show f = showAsSet $ filter (uncurry $ flip f) $ cartesian (domain f) (domain f)


instance Show ((E->T)->T) where
  show = bla

instance Show ((E->T) -> (E->T)->T) where
  show = bla2

instance Show (((E->T)->T)->T) where
  show f = showAsSet $ filter f (domain f)


case_eq a b = (map toLower a) == (map toLower b)

