{-# LANGUAGE DeriveDataTypeable, TypeFamilies, FlexibleInstances, FlexibleContexts, GeneralizedNewtypeDeriving, DeriveGeneric, TypeOperators, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, TypeFamilies #-}
module FrameUtils where

import Frame
import Data.Dynamic
import Data.Typeable

import qualified GHC.Generics as Generics

import Data.Maybe
import Data.List
import Data.Char

import Data.Tuple.Curry

-- Logical implication
(===>) :: T -> T -> T
True ===> False = False
_    ===> _     = True

-- Quantifiers
exists,forall :: (FrameType a) => ( a -> T ) -> T
exists f  = any f (domain f)
forall f  = all f (domain f)

-- Cartesian product
cartesian a b = [ (x,y) | x <- a , y <- b ]

--newtype Atomic a = Atomic { el :: a } deriving (Eq,Show)

-- instance (Enum a, Bounded a) => Finite (Atomic a) where
 --  allValues = map Atomic [(minBound) .. (maxBound)]

{-- FrameType defines which types are used in the frame,
    and provides extra functionality for those types.  -}
class (Typeable f,Eq f) => FrameType f  where
  type DomainType f
  type TargetType f
  data FTree      f
  domainElem        :: f -> (DomainType f)
  targetElem        :: f -> (TargetType f)
  homset            :: f -> [f]
  domain            :: f -> [DomainType f]        -- source object
  target            :: f -> [TargetType f]        -- target object
  image             :: f -> [TargetType f]
  showI             :: f -> String
  treeI             :: f -> (FTree f )

  hide              :: (Typeable f) => f ->  Denotation
  uncover           :: Denotation -> Maybe f

  hide              = Sem . toDyn
  uncover           = fromDynamic . unSem

  domainElem f = head (domain f)
  targetElem f = head (target f)

instance FrameType E  where
  data FTree E  = LeafE E
  type DomainType E = E
  type TargetType E = E
  domain _        = entities
  target _        = entities
  homset _ = entities
  image _         = entities
  treeI           = LeafE
  showI = show

instance FrameType Integer  where
  data FTree Integer  = LeafInt Integer
  type DomainType Integer = Integer
  type TargetType Integer = Integer
  domain _        = [0..]
  target _        = [0..]
  homset _ = [0..]
  image _         = [0..]
  treeI           = LeafInt
  showI = show


instance FrameType T where
  data FTree T  = LeafT T
  type DomainType T = T
  type TargetType T = T
  domain _        = truthvalues
  target _        = truthvalues
  homset _ = truthvalues
  image _         = truthvalues
  treeI           = LeafT
  showI = show

instance (FrameType a ,FrameType b ) => FrameType (a->b) where
  type DomainType (a->b) = a
  type TargetType (a->b) = b
  data FTree (a->b) = FSplit [(a , FTree b)]
  domain f          = homset (domainElem f)
  target f          = homset (targetElem f)
  image f           = nub $ map f (homset (domainElem f))
  homset f = functionSpace (domain f) (target f)
  showI f = concatMap (\x -> ( (showI x) ++ "|->" ++ (showI ( f x )) ++ "\n"  )) (domain f)
  treeI f = FSplit [ (x,treeI $ f x) | x <- (domain f) ]


instance (FrameType a ,FrameType b ) => FrameType (a,b) where
  type DomainType (a,b) = (a, b)
  type TargetType (a,b) = (a,b)
  data FTree (a,b) = FPair (FTree a , FTree b)
  domain (a,b)      = cartesian (homset a) (homset b)
  target (a,b)      = cartesian (homset a) (homset b)
  image  (a,b)      = cartesian (homset a) (homset b)
  homset  (a,b)      = cartesian (homset a) (homset b)
  showI (a,b) = concat [ "(" ,  showI a, showI b,  ")" ]
  treeI (a,b) = FPair (treeI a, treeI b)

instance (FrameType a ,FrameType b , FrameType c ) => FrameType (a,b,c) where
  type DomainType (a,b,c) = (a,b,c)
  type TargetType (a,b,c) = (a,b,c)
  data FTree (a,b,c) = FThree (FTree a , FTree b,FTree c)
  domain (a,b,c)      = [ (x,y,z) | x <- (homset a) , y <- (homset b) , z <- (homset c) ]
  target (a,b,c)      = [ (x,y,z) | x <- (homset a) , y <- (homset b) , z <- (homset c) ]
  image  (a,b,c)      = [ (x,y,z) | x <- (homset a) , y <- (homset b) , z <- (homset c) ]
  homset  (a,b,c)      = [ (x,y,z) | x <- (homset a) , y <- (homset b) , z <- (homset c) ]
  showI (a,b,c) = concat [ "(" ,  showI a, showI b,showI c,  ")" ]
  treeI (a,b,c) = FThree (treeI a, treeI b,treeI c)

instance (FrameType a,FrameType b) => Eq (a -> b) where
  f == g = all (\x -> (f x == g x) ) (domain f)

spacer n = take 5 $ repeat ' '
instance Show (FTree E) where showsPrec p (LeafE x) i = i++spacer p ++ show x ++ "\n"
instance Show (FTree T) where showsPrec p (LeafT x) i = i++spacer p ++ show x ++ "\n"
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
          | t == typeE   = show . fromJust $  ((fromDynamic x) :: Maybe (E))
          | t == typeT   = show $ fromJust $ ((fromDynamic x) :: Maybe (T))
          | t == typeET  = show $ fromJust $ ((fromDynamic x) :: Maybe (E -> T))
          | t == typeEET = show $ fromJust $  ((fromDynamic x) :: Maybe (E -> E -> T))
          | t == typeETT  = show $ fromJust $  ((fromDynamic x) :: Maybe ((E->T)->T))
          | t == typeListE  = show $ fromJust $  ((fromDynamic x) :: Maybe ([E]))
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
          | t == typeE    = show $ fromJust $  ((fromDynamic x) :: Maybe (E))
          | t == typeT    = show $ fromJust $ ((fromDynamic x) :: Maybe (T))
          | t == typeTT   = show $ fromJust $ ((fromDynamic x) :: Maybe (T -> T))
          | t == typeET   = showFunctionAsSet $ fromJust $ ((fromDynamic x) :: Maybe (E -> T))
          | t == typeEET  = show $ fromJust $  ((fromDynamic x) :: Maybe (E -> E -> T))
          | t == typeETET = show $ fromJust $  ((fromDynamic x) :: Maybe ((E -> T) -> E -> T))
      --    | t == typeETT  = bla $fromJust$  ((fromDynamic x) :: Maybe ((E->T)->T))
          | t == typeListE  = show $ fromJust $  ((fromDynamic x) :: Maybe ([E]))
          | otherwise =  "~"

showFunctionAsSet f = showAsSet $ filter f (domain f)
showAsSet x = (\x -> "{"++x++"}") $ concat $ intersperse "," $  map show x
showAsSetAbbr x = (\x -> "{"++x++"}") $ concat $ intersperse "," $  map (take 2 . show) x
asSet2 x = (\x -> "{"++x++"}\n") $ concat $ intersperse "," x

bla f = asSet2 $ map asSet2 $ (map.map) (take 2 . show) ents
  where
    sets = filter f (domain f)
    ents = map (\x -> filter x (domain x)  ) sets

bla2 f =  asSet2 $ map (\(a,b) -> concat ["(",showAsSetAbbr a," , ",showAsSetAbbr b,")\n"] ) ents
  where
    sets = filter (uncurry f) (cartesian (domain f) (domain f))
    ents = map (\(x,y) -> (filter x (domain x),filter y (domain y))  ) sets

instance Show (E->T) where
  show f = showAsSet $ filter f (domain f)
instance Show (T->T) where
  show f = showAsSet $ filter f (domain f)

instance Show ((E->T)-> E ->T) where
  show f
    | isId f    = "'identity function'"
    | otherwise = "~" -- show $ map (\x -> concat $ [show x,"|->",show $ f x]) (domain f)

instance Show (E->E->T) where
  show f = showAsSet $ filter (uncurry $ flip f) $ cartesian (domain f) (domain f)


instance Show ((E->T)->T) where
  show = bla

instance Show ((E->T) -> (E->T)->T) where
  show = bla2

instance Show (((E->T)->T)->T) where
  show f = showAsSet $ filter f (domain f)


case_eq a b = (map toLower a) == (map toLower b)



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

entry :: (FrameType sem,SyntacticType syn ,CorrespondingTypes syn sem)
      => String -> syn -> sem  -> LexiconEntry
entry string syntax denotation = (string,wrap syntax, hide denotation,[])


entryString (str,syn,den,mp) =
    [ dbracket $ show str ," = ",show den," ",showType den ,"\n",show syn]
entryArr (str,syn,den,mp) =
     [ show str , " | "
     , show syn     , "|"
     , showType den   , "|"
     , show den       , "|"
     , if not $ null mp then unwords $ map show mp else ""
      ]

instance Show Lexicon where
  show lexicon =  unlines $ map space rows  where
    rows    = map entryArr (entries lexicon)
    widths  = foldr (zipWith max . map length) [0..] $ rows
    space   = concat . map (trimTo 40) . zipWith fillTo widths
    fillTo n string = take n $ string ++ repeat ' '
    trimTo n string = if length string > n then (take (n-3) string) ++ "..." else string

data MP = MP String Denotation
instance Show MP  where show (MP str _) = str
instance Eq MP    where (MP a _) == (MP b _) = a == b



type LexiconEntry = (String, SynCat, Denotation, [MP])
newtype Lexicon = Lexicon { entries :: [LexiconEntry] }
