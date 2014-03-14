module Parser where

import Frame
import FrameUtils
import Lexicon
import Data.List
import Data.Char
import Data.Maybe
import Data.Dynamic
import Data.Typeable
import Control.Monad
import Text.PrettyPrint hiding (Mode,cat)

-- Parses a sentence and shows the derivations (as decorated syntax trees)
parse :: [Char] -> IO ()
parse sentence
 | size == 0 	= putStrLn "The sentence could not be completely parsed"
 | size == 1 	= putStrLn $ "There is one derivation for " ++ show sentence ++ " :\n" ++  derivations
 | otherwise	= putStrLn $ "There are "++show size++" derivations for " ++ show sentence ++ " :\n"++ derivations
 where
    n = length $ words sentence
    succes (Split x _ _) = start x == 0 && end x == n
    succes (Extend x _)  = start x == 0 && end x == n
    succeses = filter succes $ (fst3 . run_ptree ) sentence
    derivations =   render $ foldr1 ($$) $ map prettyprint succeses
    size = length succeses

-- try : returns the top result in the parsing proces
-- this is handy for trying incomplete sentences.
try :: [Char] -> IO ()
try input = putStr (concat [show item , "\n" , show denotation]) where
   (item, denotation) = run_parser input

{- An Item is used for representing linguistic resources in the parser.
 It is a 6-tuple consisting of:
 * a left index, a categorial type, a String, a denotation,
 * ,meaning postulates and a right index -}
data Item
  = Item
  { start  :: Int
  , cat    :: SynCat
  , str    :: String
  , den    :: Denotation
  , mps    :: [MP]
  , end    :: Int
  }

-- two Items are equal when their indices, categories and strings match
instance Eq Item where a == b = and [num_eq a b,cat_eq a b,str_eq a b]
-- Items can also be equal in index, category and string
num_eq a b = start a == start b && end a == end b
cat_eq a b = cat a == cat b
str_eq a b = str a == str b


-- Items are adjacent if the right and left index are equal
adjacent l r = end l == start r


-- Charts and agenda's are lists of items
newtype Chart  = Chart  { unchart :: [Item] }
newtype Agenda = Agenda [Item]

-- Rules combine 2 items to none or multiple items
type Rule   = Item -> Item -> [Item]

-- The tree datatype for representing deductions
data Tree a
	= Nil
	| Extend a (Tree a)
	| Split  a (Tree a) (Tree a)    deriving (Show,Eq)

top (Split a _ _) = a
top (Extend a _ ) = a

prettyprint :: Tree Item -> Doc
prettyprint x = prettyPrintT $ path [] x

ppItem_a, ppItem_b :: Item -> Doc
ppItem_a item
	= (hsep $ map text [str item," :: ",show $ cat item," :: ",showType $ den item] ) -- (text $ show cat)

ppItem_b (Item i cat str sem mp j)
	= (hsep $ map text ["den. = ",show sem] ) -- (text $ show cat)
	where n = ((length str) )- (length $ show cat)

spacea x = text $ take x (repeat ' ')

data Direction = L | R | D deriving (Show,Eq)
type Path = [Direction]

path :: Path -> Tree Item -> Tree (Path,Item)

path ls (Extend x Nil) = Extend (ls,x) Nil
path ls (Extend x a)   = Extend (ls,x) (path (ls++[D]) a)
path ls (Split x Nil Nil) = Split (ls,x) Nil Nil
path ls (Split x l r) =
	Split (ls,x)
		(path (ls++[L]) l)
		(path (ls++[R]) r)

ppMode flag path = case (flag,path) of
  ( _     , []  )  -> empty
  ( b     , (L:t) ) -> bar <> ppMode b t
  ( b     , (D:t) ) -> tab <> ppMode b t
  ( b     , (R:t) ) -> tab <> ppMode b t
  -- terminal nodes
  ( False , [R] ) ->  mtab <> ends
  ( True  , [R] ) ->  tab
  ( False , [L] ) ->  mtab <> vr
  ( True  , [L] ) -> bar
  ( True  , [D] ) -> bar
  ( False , [D] ) ->  mtab <> vr


prettyPrintT (Split (m,i) Nil Nil) =
     (if m /= [] && last m == L then ppMode True m else empty)
 $+$ ppMode False m  <> dot <> space <> ppItem_a i
 $+$ ppMode True m <> space <> dot'  <> space <> ppItem_b i
 $+$ ppMode True m

prettyPrintT (Split (m,i) l r) =
     ppMode False m <> space <> ppItem_a i
 $+$ ppMode True m <> space <> space <> ppItem_b i
 $+$ prettyPrintT l
 $+$ prettyPrintT r

prettyPrintT (Extend (m,i) Nil ) =
   ppMode True m <> space <> ppItem_a i
-- $+$ ppMode True m <> space <> space <> ppItem_b i
 -- $+$ ppMode True m <> mtab <> pipe


prettyPrintT (Extend (m,i) l ) =
     ppMode False m <> space <> ppItem_a i
 $+$ ppMode True m <> space <> space <> ppItem_b i
 $+$ ppMode True m <> mtab <> pipe
 $+$ prettyPrintT l

tab   = spacea 4
mtab  = spacea 3
ltab  = linea 2
hltab = linea 0

linea x = text $ take x (repeat '-')--(chr 9473))

sp3 = text "  "
pipe = text "|" --[chr 9475]
ends = text "\\="  -- [chr 9495] <> line  -- text "\\"
bar = mtab <> pipe

vr    = text "|=" --text [chr 9507]
line  = text "="	--text [chr 9473]
cross = text "+"  --text [chr 9523]
block = text "#"  --text [chr 9608]
circ  = text "o"  --text [chr 9675]
dot   = text "o"	--text [chr 9675]
dot'  = text ""   --text [chr 9675]

instance Show Item where
  show (Item i cat str sem  mp j) =
  	(cbracket.unwords $ [show i,show cat,str,show $ sem,show j] ) ++"  "++show mp
instance Show Chart  where
 	show (Chart  x) = concat $ intersperse "\n" $ "Chart:" : map show x
instance Show Agenda where
	show (Agenda x) = concat $ intersperse "\n" $ "Agenda:": map show x


---- Deduction rules
-- Here the deduction rules are defined, based on the natural deduction format,
-- showing, in parallel, combination of catergory, type, denotation, and meaning postulates

{- 	function application for hidden denotations.
	This function seems unsafe, but since the grammar rules guarantees
	that all uses of this function are valid, only valid uses occur -}
apply :: Denotation -> Denotation -> Denotation
apply (Sem function) (Sem arg) = Sem $ dynApp function arg

{- 	Pairing for hidden denotations. -}
pair :: Denotation -> Denotation -> Denotation
pair l r = l

-- The 3 deduction rules of AB_CYK_product
rule_AppLeft,rule_AppRight :: Rule
--			|  |SynCat	  |String|Denotation      |Type     |MP	   |  |
rule_AppLeft
  left@( Item i  b        m      x                ma 	    	k )
 right@( Item k' (b':\:a) n      f                mb        j ) =
 -- --------|--|------|------|---------|---------|---------|--|
     if adjacent left right && b==b'  then
 -- --------|--|------|------|---------|---------|---------|--| \ elimination
      [( Item i      a  (m+++n)  (apply f x)  	 (ma.+.mb)  j )]  else []
rule_AppLeft _ _ = []

rule_AppRight               -- (F f (a:->tb)) and (s) = f s
  left@(Item i (a:/:b)  m      f          ma 	    k )
 right@(Item k'     b'  n      x          mb 	    j ) =
 -- --------|--|------|------|---------|---------|---------|--|
  if adjacent left right && b==b'  then
 -- --------|--|------|------|---------|---------|---------|--| / elimination
      [(Item i  a     (m+++n)(apply f x)  	  (ma.+.mb) j )]  else []
rule_AppRight _ _ = []

rule_Pair subformulas
  left@(Item i  a      m      l          		ma 		    k )
 right@(Item k' b 	   n      r          		mb 		    j ) =
 -- --------|--|------|------|---------|---------|---------|--|
  if adjacent left right && (a:*:b) `elem` subformulas then
 -- --------|--|------|------|---------|---------|---------|--| * introduction
      [(Item i (a:*:b) (m.*.n)(pair l r) (ma.+.mb)  j )]  else []


-- combining strings with bracketing for display purposes of derived items
(+++) :: String -> String -> String
a +++ b = bracket  $ a ++ " " ++ b  -- for application
a .*. b = bracket  $ a ++ "*" ++ b  -- for pairing

-- combining Meaning Postulates (union)
(.+.) :: (Eq a) => [a] -> [a] -> [a]
a .+. b = a `union` b

-- combine the rules into a single function
rules1 x   sub = concatMap (\f -> f x) [] -- [rule_Lift]

rules x y sub = concatMap (\f -> f x y) all_rules where
	all_rules = baserules ++ map flip baserules
	baserules = [rule_Pair sub,rule_AppRight ,rule_AppLeft]

-- The parsing procedure
run_parser :: String -> (Chart, Agenda)
run_parser sentence = exhaust_agenda (Chart [] ,Agenda (itemize sentence) )

-- a Agenda-driven chart-based parser
-- Based on "Parsing with Structure-Preserving Categorial Grammars" p. 79
exhaust_agenda (a,Agenda i) =
	(\(l,r,_) -> (l,r) ) (exhaust_agenda' (a,Agenda i,subformulas i))

exhaust_agenda' :: (Chart, Agenda, [SynCat]) -> (Chart, Agenda, [SynCat])
exhaust_agenda' (Chart chart , Agenda [] , sub) =
  (Chart chart , Agenda [] , sub) -- stop when the agenda is empty
exhaust_agenda' (Chart chart , Agenda (agenda_head:agenda_tail), subfs)
  -- the next item on the agenda is already known: proceed to next item
  | agenda_head `elem` chart = (Chart chart,Agenda agenda_tail , subfs)
  -- generate new items based on current chart and head of agenda and recur
  | otherwise = let
     -- apply all rules to the current chart and head of the agenda
     generated  = [ result | chart_item <- chart , result <- rules chart_item agenda_head subfs]
     next       = (Chart $ [agenda_head] `union` chart,
                   Agenda (generated `union` agenda_tail)  ,
                   subfs)
     in exhaust_agenda' next

ptree' (chart , []    	   ,sub) = ( chart ,[],sub)
ptree' (chart , (y:agenda) , sub)
	|  y `elem` chart 	= ptree' (chart   ,agenda   ,sub)
	| otherwise		= ptree' (newchart,newagenda,sub)
	where
		produced  =  [ (Split result z y) | z <- chart , result <- rules (top z) (top y) sub ]
		produced2  = [ (Extend result y) | result <- rules1 (top y) sub ]
		newagenda = agenda `union` produced `union` produced2
		newchart  = [y] `union` chart

run_ptree sent = ptree' ( [] , map (\x -> Split x Nil Nil) items, subformulas items)
	where items = itemize sent
fst3 (a,_,_) = a

-- Subformula computation for product formula's
data Polarity = Plus | Min deriving (Eq, Show)

subform :: Polarity -> SynCat -> [SynCat]
subform Plus (a :*: b) = concat [ [a :*: b] , subform Plus a , subform Plus b ]
subform Min  (c :/: x) = case x of
	(a :*: b ) -> subform Plus x ++ subform Min c
	_	   -> subform Min c
subform _ _ = []

subformulas :: [Item] -> [SynCat]
subformulas items = concatMap (\x -> subform Min (cat x)) items


-- lexical_lookup: return the matching entries in the lexicon. case is ignored
lexical_lookup :: Lexicon -> String -> [(SynCat,Denotation,[MP])]
lexical_lookup lex x
   | null results = error (show x ++ " not found in lexicon")
   | otherwise    = results
   where results =  [ (cat,den,mp) | (str,cat,den,mp) <- entries lex , case_eq x str ]
         case_eq a b = (map toLower a) == (map toLower b)

--itemize takes a string and attempts to make a list of indexed items, starting at 0
itemize :: String -> [Item]
itemize str = itemize' 0 (words str)

-- itemize' makes a list of numbered items from a list with number n
itemize' :: Int -> [String] -> [Item]
itemize' i [] = []
itemize' i (word:ws) = makeItem i word ++ itemize' (i+1) ws

-- creates numbered items by looking up a string in the lexicon
makeItem :: Int -> String -> [Item]
makeItem num str = [ Item num cat str sem  mp (num+1) |  (cat,sem,mp) <- lexical_lookup lexicon str ]

getEntry :: String -> IO ()
getEntry string = sequence_ $ do
  entry@(str,syn,den,mp) <- entries lexicon
  guard ( str `case_eq` string )
  return (putStrLn . show $ entryString entry)
