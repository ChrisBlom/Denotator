{-# LANGUAGE TypeSynonymInstances #-}

{- Haskell Lexicon - Chris Blom - HW 5 version -}

{- Please fill in you name and student number here:

   name:
   student number:

   If your use ghci, start it like this:
    ghci -fglasgow-exts -XTypeFamilies
   If you use winhugs,
    Enter this at File, Options, GHC startup:
    ghc --interactive -fglasgow-exts -XTypeFamilies

   Then, once you started ghci, enter:
    :load Parser
   to load the lexicon and parser

   (Please contact Chris if you have any trouble opening or loading this file or ghci)
   -}
module Lexicon where

import Data.Maybe
import Data.List
import Control.Monad

import Frame
import FrameUtils
import Syntax


{---- Boolean Type Class --------------------------------}
infix 8 /\
infix 8 \/

class (FrameType a) => Boolean a where
  (/\)  :: a -> a -> a -- and
  (\/)  :: a -> a -> a -- or
  compl :: a -> a      -- not
  (.<.) :: a -> a -> T -- numerical order
  one   :: a
  zero  :: a

---- T is a Boolean type
instance Boolean T where
  x /\ y   = x && y
  x \/ y   = x || y
  compl x  = not x
  x .<. y  = x ==> y
  one      = True
  zero     = False

----  if type b is Boolean  then (a->b) is Boolean as well
instance (FrameType a,Boolean b) => Boolean (a -> b) where
  f /\ g   = \x -> f x /\ g x
  f \/ g   = \x -> f x \/ g x
  compl f  = \x -> compl (f x)
  f .<. g  = forall ( \x -> f x .<. g x )
  one      = \x -> one
  zero     = \x -> zero

{---- Combinators and Utility Functions -----------------}

-- charf takes a set of entities and returns its characteristic function
charf :: [E] -> E -> T
charf = \set -> \x -> x `elem` set

-- charf2 takes a relation and returns its characteristic function
charf2 :: (Eq a,Eq b) => [(a,b)] -> (b -> a -> T)
charf2 = \relation -> \y -> \x -> (x,y) `elem` relation

-- list : takes an entity x and return the GQ for that entity x,
--        (which is the char. function of all subsets of E that x is in)
lift :: E -> (E->T)->T
lift = \x -> \f -> f x

-- Quantifiers
exists,forall :: (FrameType a) => ( a -> T ) -> T
exists f  = any f (domain f)
forall f  = all f (domain f)

{- toList : takes a boolean function f and returns a list
   of all arguments for which f returns True
   (it returns the set that f characterizes) -}
toList f = filter f (domain f)

{- card : takes a characteristic function f and return the
   number of arguments for which f returns True
   (it return the cardinality of the set that f characterizes) -}
card f = length (toList f)

{---- Denotations ---------------------------------------}

{- Homework 4.3: 
    (make 4.1 and 4.2 below first) -}
{- Redefine the denotations below, such that all the 6 sentences below are all true.
   (You can use the Parser to compute the sentence meaning,
    for example by entering:
      parse (sentence 1)
    )
-}

sentence 1  = "at_most 3 boys love leia"
sentence 2  = "at_least 1 girl runs"
sentence 3  = "exactly 1 alien loves Han"
sentence 4  = "few boys are boys and tall"
sentence 5  = "most boys love leia"
sentence 6  = "many aliens are thin"
sentence 7  = "at_least 2 boys and ^ leia are human"

{- denotations to edit: -}
boy,girl,human,alien :: E -> T
boy     = charf [Luke,Han,Yoda,Chewbacca,Vader]
girl    = charf [Leia]
human   = charf [Han,Luke,Leia,Vader]
alien   = compl human
thin    = charf [Yoda,Leia]
jedi    = charf [Luke,Vader]
short   = charf [Yoda,Leia]
tall    = charf [Han,Vader,Chewbacca]
ran     = charf [Han,Luke]
average_sized = compl (tall \/ short)

loves,hates,is_conflicted_about,does_not_care_about :: E -> E -> T
loves = charf2 [ (Han,Leia) , (Leia,Luke) , (Luke,Leia) , (Han,Chewbacca)
               , (Vader,Luke) , (Chewbacca,Han)  ]
hates = charf2 ( [ (Vader,Luke) , (Vader,Han) ] `union` cartesian entities [Vader])

is_conflicted_about = loves /\ hates
does_not_care_about = compl (loves \/ hates)

{---- Denotations of GQ and DET's--------}

-- examples:
every :: (E->T) -> (E->T) -> T
every f g = f .<. g

some :: (E->T) -> (E->T) -> T
some f g = exists (f /\ g)

no :: (E->T) -> (E->T) -> T
no f g = card (f /\ g) == 0

everyone :: (E->T) -> T
everyone f = forall f

someone :: (E->T) -> T
someone f = card f > 0

no_one :: (E->T) -> T
no_one f = no one f


{- Homework 4.2 :
   Define denotations for most, many , few and add lexicon entries.
   See the lecture notes on GQ's and Keenan for hints on what the denotations should be.
   To give these denotatios as haskell terms, take a good look at the example above and
   the utility functions.
   Hint: you can use the polymorhic boolean types and any of the utility functions -}

--most :: (E->T) -> (E->T) -> T
--most

--many :: (E->T) -> (E->T) -> T
--many

--few :: (E->T) -> (E->T) -> T
--few

{- Homework 4.3 :
   define a denotation for 'exactly', that takes a Integer n (a integer number), and
   two f and g (characterizing sets of entities) and returns
   True if the intersection of these sets is of size n.
   Also add the lexicon entry.
   Hint: you can use the polymorhic boolean types and any of the utility functions such as card
   -}

--exactly :: Integer -> (E->T) -> (E->T) -> T
--exactly

{- Define similar denotations for at_least and at_most and uncomment the lexicon entries -}

--at_least :: Integer -> (E->T) -> (E->T) -> T
--at_least

--at_most :: Integer -> (E->T) -> (E->T) -> T
--at_most


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
adn     = N :/ N          -- adnominals : take a noun, return a noun 
adv     = iv :\ iv        -- adverbs
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
  , entry "boy"       n                           boy
  , entry "boys"      n                           boy
  , entry "girl"      n                           girl
  , entry "girls"     n                           girl
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

--  , entry "few"     det                             no
--  , entry "many"    det                             no
--  , entry "most"    det                             no

--  , entry "exactly"     (det:/num)                  exactly
--  , entry "at_most"     (det:/num)                  at_most
--  , entry "at_least"     (det:/num)                 at_least

{- Coordinations -}
-- TODO : find out how to use polymorphism in the lexicon: this is awful!
  , entry "and"       ((s:\s):/s)               ( (/\) :: T -> T -> T )
  , entry "or"        ((s:\s):/s)               ( (\/) :: T -> T -> T )
  , entry "it_is_not_the_case_that" (s:/s)      ( compl :: T -> T )

  , entry "and"       ((gq:\gq):/gq)               ( (/\) :: GQ -> GQ -> GQ)
  , entry "or"        ((gq:\gq):/gq)               ( (\/) :: GQ -> GQ -> GQ )
  , entry "it_is_not_the_case_that" (gq:/gq)      ( compl :: GQ -> GQ )

  , entry "and"       ((n:\n):/n)               ( (/\) :: (E->T)->(E->T)->(E->T))
  , entry "or"        ((n:\n):/n)               ( (\/) :: (E->T)->(E->T)->(E->T))
  , entry "not"       (n:/n)                    ( compl :: (E->T) -> (E->T) )

  , entry "and"       ((iv:\iv):/iv)            ( (/\) :: (E->T)->(E->T)->(E->T))
  , entry "or"        ((iv:\iv):/iv)            ( (\/) :: (E->T)->(E->T)->(E->T))
  , entry "not"       (iv:/iv)                  ( compl :: (E->T) -> (E->T) )

  , entry "and"       ((adv:\adv):/adv)            ( (/\) :: (ET->ET)->(ET->ET)->(ET->ET))
  , entry "or"        ((adv:\adv):/adv)            ( (\/) :: (ET->ET)->(ET->ET)->(ET->ET))
  , entry "not"       (adv:/adv)                  ( compl :: (ET->ET)->(ET->ET) )

  , entry "and"       ((det:\det):/det)            ( (/\) :: DET->DET->DET)
  , entry "or"        ((det:\det):/det)            ( (\/) :: DET->DET->DET)
  , entry "not"       (det:/det)                  ( compl :: (DET->DET) )

  , entry "and"       ((gq:\gq):/gq)            ( (/\) :: GQ->GQ->GQ)
  , entry "or"        ((gq:\gq):/gq)            ( (\/) :: GQ->GQ->GQ)
  , entry "not"       (gq:/gq)                  ( compl :: (GQ->GQ) )
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














