{-# LANGUAGE TypeSynonymInstances #-}

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
-- Converts a collection to its characteristic function.
-- Takes a set of entities,
-- returns a function that takes
--    an entity,
--    returns true iff the entity is in the set or false otherwise
isIn :: [E] -> E -> T
isIn set = \x -> x `elem` set

-- isIn2 takes a relation and returns its characteristic function
isIn2 :: (Eq a,Eq b) => [(a,b)] -> (b -> a -> T)
isIn2 relation = \y -> \x -> (x,y) `elem` relation


{---- Combinators and Utility Functions -----------------}

-- list : takes an entity x and return the GQ for that entity x,
--        (which is the char. function of all subsets of E that x is in)
lift :: E -> (E->T)->T
lift = \x -> \f -> f x


{- toList : takes a boolean function f and returns a list
   of all arguments for which f returns True
   (it returns the set that f characterizes) -}
toList f = filter f (domain f)

{- cardinality : takes a characteristic function f and return the
   number of arguments for which f returns True
   (it return the cardinality of the set that f characterizes) -}
cardinality f = length (toList f)

{---- Denotations ---------------------------------------}

{- denotations to edit: -}
human,alien :: E -> T

human   = isIn [Han,Luke,Leia,Vader]
alien   = complement human

jedi    = isIn [Luke,Vader]
short   = isIn [Yoda,Leia]
tall    = isIn [Han,Vader,Chewbacca]
thin    = isIn [Leia,Yoda]
ran     = isIn [Han,Luke]
average_sized = complement (tall \/ short)

loves,hates,is_conflicted_about,does_not_care_about :: E -> E -> T
loves = isIn2 [ (Han,Leia) , (Leia,Luke) , (Luke,Leia) , (Han,Chewbacca)
               , (Vader,Luke) , (Chewbacca,Han)  ]
hates = isIn2 ( [ (Vader,Luke) , (Vader,Han) ] `union` cartesian entities [Vader])

is_conflicted_about = loves /\ hates
does_not_care_about = complement (loves \/ hates)

{---- Denotations of Generalized Quantifiers and determiners--------}

-- examples:
every :: (E->T) -> (E->T) -> T
every f g = f .<. g

some :: (E->T) -> (E->T) -> T
some f g = exists (f /\ g)

no :: (E->T) -> (E->T) -> T
no f g = cardinality (f /\ g) == 0

everyone :: (E->T) -> T
everyone f = forall f

someone :: (E->T) -> T
someone f = cardinality f > 0

no_one :: (E->T) -> T
no_one f = no one f

{---- Type Abbreviations --------------------------------}
type ET  = E -> T         -- E -> T
type GQ  = ET -> T        -- generalized quantifiers
type DET = ET -> ET -> T  -- determiners

{---- Lexicon -------------------------------------------}

-- some abbreviations for common syntactic categories
--        definition      category:
n       = N               -- nouns
num     = NUM             -- numbers
s       = S               -- sentences
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
{- the lexicon : a list of Strings associated with their syntactic category and denotation -}


{-----------------------------------------------------------------
The Lexicon: this is the lexicon where all the entries are defined.
A lexicon is a list of words, associated with their denotation and syntactic type
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
  , entry "aliens"    n                           alien
  , entry "average_sized"  n                      average_sized

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

{- Coordinations -}
-- TODO : find out how to use polymorphism in the lexicon: this is awful!
  , entry "and"       ((s:\s):/s)               ( (/\) :: T -> T -> T )
  , entry "or"        ((s:\s):/s)               ( (\/) :: T -> T -> T )
  , entry "it_is_not_the_case_that" (s:/s)      ( complement :: T -> T )

  , entry "and"       ((gq:\gq):/gq)               ( (/\) :: GQ -> GQ -> GQ)
  , entry "or"        ((gq:\gq):/gq)               ( (\/) :: GQ -> GQ -> GQ )
  , entry "it_is_not_the_case_that" (gq:/gq)      ( complement :: GQ -> GQ )

  , entry "and"       ((n:\n):/n)               ( (/\) :: (E->T)->(E->T)->(E->T))
  , entry "or"        ((n:\n):/n)               ( (\/) :: (E->T)->(E->T)->(E->T))
  , entry "not"       (n:/n)                    ( complement :: (E->T) -> (E->T) )

  , entry "and"       ((iv:\iv):/iv)            ( (/\) :: (E->T)->(E->T)->(E->T))
  , entry "or"        ((iv:\iv):/iv)            ( (\/) :: (E->T)->(E->T)->(E->T))
  , entry "not"       (iv:/iv)                  ( complement :: (E->T) -> (E->T) )

  , entry "and"       ((adv:\adv):/adv)            ( (/\) :: (ET->ET)->(ET->ET)->(ET->ET))
  , entry "or"        ((adv:\adv):/adv)            ( (\/) :: (ET->ET)->(ET->ET)->(ET->ET))
  , entry "not"       (adv:/adv)                  ( complement :: (ET->ET)->(ET->ET) )

  , entry "and"       ((det:\det):/det)            ( (/\) :: DET->DET->DET)
  , entry "or"        ((det:\det):/det)            ( (\/) :: DET->DET->DET)
  , entry "not"       (det:/det)                  ( complement :: (DET->DET) )

  , entry "and"       ((gq:\gq):/gq)            ( (/\) :: GQ->GQ->GQ)
  , entry "or"        ((gq:\gq):/gq)            ( (\/) :: GQ->GQ->GQ)
  , entry "not"       (gq:/gq)                  ( complement :: (GQ->GQ) )
  ]

------------------------------------------------------------------
-- Dont change anything below this line
------------------------------------------------------------------
    {-
checkMP :: [f] -> (f->T) -> Bool
checkMP functions  mp = not . null $ filter mp functions


(.|.) :: (FrameType f) => LexiconEntry -> (String,f) -> LexiconEntry
(str,syn,den,mp) .|. (des,mp2) = (str,syn,den,(MP des $ hide mp2) : mp)


entry :: (FrameType t,SyntacticType s ,CorrespondingTypes s t)
      => String -> s -> t  -> LexiconEntry
      -}
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
    widths  = foldr (zipWith max . map length ) [0..] $ rows
    space   = concat . map (trimTo 40) . zipWith fillTo widths
    fillTo n string = take n $ string ++ repeat ' '
    trimTo n string = if length string > n then (take (n-3) string) ++ "..." else string

data MP = MP String Denotation
instance Show MP  where show (MP str _) = str
instance Eq MP    where (MP a _) == (MP b _) = a == b














