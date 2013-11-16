{-# LANGUAGE TypeSynonymInstances, TemplateHaskell #-}

{- In this module the functions to compute the meanings of words are defined,
   along with their syntactic rules.
-}
module Lexicon where

import Data.Maybe
import Data.List
import Control.Monad

import Quantifiers
import Frame
import FrameUtils
import Syntax
import Boolean


import Test.QuickCheck

deepCheck n = verboseCheckWith (stdArgs { maxSuccess = n , chatty = True})

-- Takes a set and returns is characteristic function.
-- Takes a set of entities,
-- returns a function that takes
--    an entity,
--    returns true iff the entity is in the set or false otherwise
charfun :: [E] -> E -> T
charfun set = \x -> x `elem` set

-- charfun_rel takes a relation and returns its characteristic function
cahrfun_rel :: (Eq a,Eq b) => [(a,b)] -> (b -> a -> T)
cahrfun_rel relation = \y -> \x -> (x,y) `elem` relation

-- lift : takes an entity x and return the GQ for that entity x,
--        (which is the char. function of all subsets of E that x is in)
lift :: E -> (E->T)->T
lift = \x -> \f -> f x

{- toList : takes a boolean function f and returns a list
   of all arguments for which f returns True
   (it returns the set that f characterizes) -}
toList f = filter f (domain f)

{- cardinality : takes a characteristic function f and returns the
   number of arguments for which f returns True
   (it return the cardinality of the set that f characterizes) -}
cardinality f = length (toList f)


luke :: E 
luke = Luke

{- denotations to edit: -}
human,alien :: E -> T

human   = charfun [Han,Luke,Leia,Vader]
alien   = complement human

jedi    = charfun [Luke,Vader]
short   = charfun [Yoda,Leia]
tall    = charfun [Han,Vader,Chewbacca]
thin    = charfun [Leia,Yoda]
ran     = charfun [Han,Luke]
normal  = complement (tall \/ short)

good    = charfun [Luke,Vader,Yoda,Han,Chewbacca]
evil    = complement good

loves,hates,is_conflicted_about,does_not_care_about :: E -> E -> T
loves = cahrfun_rel [ (Han,Leia) , (Leia,Luke) , (Luke,Leia) , (Han,Chewbacca)
               , (Vader,Luke) , (Chewbacca,Han)  ]
hates = cahrfun_rel ( [ (Vader,Luke) , (Vader,Han) ] `union` cartesian entities [Vader])

fast :: (E -> T) -> (E -> T)
fast f = f /\ charfun [Luke]

is_conflicted_about = loves /\ hates
does_not_care_about = complement (loves \/ hates)

{---- Type Abbreviations --------------------------------}
type ET  = E -> T         -- E -> T
type GQ  = ET -> T        -- generalized quantifiers
type DET = ET -> ET -> T  -- determiners

{---- Lexicon -------------------------------------------}

-- some abbreviations for common syntactic categories
--        definition      category:
s       = S               -- sentences
n       = N               -- nouns
num     = NUM             -- numbers
np      = NP              -- noun phrases
iv      = np :\ s         -- intransitive verbs: require a np on the left
tv      = iv :/ np        -- transitive verbs: require a np on the left and right 
dtv     =((np:\s):/np):/np-- ditransitive verbs
adn     = N :/ N          -- adnominals : take a noun and return a noun
adv     = iv :\ iv        -- adverbs : take a verb and return a verb
det     = s :/ iv :/ n    -- determiners
gq      = s:/(np:\s)      -- generalized quantifiers

type LexiconEntry = (String, SynCat, Denotation, [MP])
newtype Lexicon = Lexicon { entries :: [LexiconEntry] }


alien_mod = (/\ alien)

{----------------------------------------------------------------- 
The Lexicon: this is the lexicon where all the entries are defined.
A lexicon is a list of triples of a word, a syntactic type and a denotation
-----------------------------------------------------------------}
lexicon = Lexicon $ [ entry (show x) num x | x <- [(1::Integer)..10] ] ++
  [
{-=== Entities ===-}
    entry "Luke"      np                         Luke
  , entry "Leia"      np                         Leia
  , entry "Chewbacca" np                         Chewbacca
  , entry "Han"       np                         Han
  , entry "Yoda"      np                         Yoda
  , entry "Vader"     np                         Vader
  , entry "^"         (gq:/np)                   lift

{-=== Copula, etc. ====-}
  , entry "is"        ((gq:\s):/gq)              ( (\f g -> exists (f /\ g )) :: GQ -> GQ -> T )
  , entry "is_a"      ((np:\s):/n)               ( (\x -> x) :: (E->T) -> (E->T))
  , entry "is"        ((np:\s):/n)               ( (\x -> x) :: (E->T) -> (E->T))
  , entry "are"       (iv:/n)               ( (\x -> x) :: (E->T) -> (E->T))
  , entry "to"        (np:/np)                   ( (\x -> x) :: E->E )
  , entry "than"      (iv:/iv)                   ( id :: (E->T) -> (E->T) )
  , entry "did"       (iv:/iv)                   ( id :: (E->T) -> (E->T) )

{-=== Nouns and Adjectives ===-}
  , entry "tall"      n                           tall
  , entry "thin"      n                           thin
  , entry "human"     n                           human
  , entry "short"     n                           short
  , entry "alien"     n                           alien
  , entry "alien"     (n:/n)                      alien_mod

{-=== Verbs and Adverbs===-}
  , entry "ran"        iv                         ran
  , entry "runs"       iv                         ran
  , entry "loves"      tv                         loves
  , entry "love"       tv                         loves
  , entry "hates"      tv                         hates
  , entry "is_conflicted_about" tv                is_conflicted_about
  , entry "does_not_care_about" tv                does_not_care_about

{-=== Determiners and GQ's ===-}
  , entry "every"     det                         every
  , entry "some"      det                         some
  , entry "no"        det                         no

  , entry "everyone"   gq                         everyone
  , entry "someone"    gq                         someone
  , entry "no_one"     gq                         no_one

{- Coordination -}
  , entry "and"       ((s:\s):/s)               ( (/\) :: T -> T -> T )
  , entry "or"        ((s:\s):/s)               ( (\/) :: T -> T -> T )
  , entry "it_is_not_the_case_that" (s:/s)      ( complement :: T -> T )
  ]

------------------------------------------------------------------
-- Dont change anything below this line
------------------------------------------------------------------
entry :: (FrameType t,SyntacticType s ,CorrespondingTypes s t)
      => String -> s -> t  -> LexiconEntry
entry string syntax denotation = (string,wrap syntax, hide denotation,[])

getEntry :: String -> IO ()
getEntry string = sequence_ $ do
  entry@(str,syn,den,mp) <- entries lexicon
  guard ( str `case_eq` string )
  return (putStrLn . show $ entryString entry)

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
