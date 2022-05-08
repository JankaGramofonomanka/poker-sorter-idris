module PatternSelection

import Data.List
import Data.List1
import Data.Vect
--import Data.Function


import Interfaces
import DataDefs
import HandOrder
import Utils



{-  `Rule` is a type of functions that represent poker rules. A function of 
    type `Rule` selects the best pattern from a hand and a board according to 
    the rule it represents.
-}
Rule : Nat -> Type
Rule n = Board -> Hand (S n) -> HandWithPattern

-- Helper functions -----------------------------------------------------------
rnk : Card -> Rank
rnk (MkCard r _) = r

suit : Card -> Suit
suit (MkCard _ s) = s


groupByRank : List Card -> List (List Card)
groupByRank l = map list1ToList $ (groupBy ((==) `on` rnk) . sort) l

partial
isStraight : Vect 5 Card -> Bool
--isStraight Nil = False
isStraight cards = let

    sorted = sortVect cards
    (first :: rest) = sorted

    nats : Vect 4 Nat
    --nats = 1 :: map (1 +) nats
    nats = [1, 2, 3, 4]

    zipped : Vect 4 (Nat, Card)
    zipped = zip nats rest

    inPlace : Card -> (Nat, Card) -> Bool
    inPlace first (dist, card)
      =   fromEnum (rnk first) + dist == fromEnum (rnk card)
      ||  (rnk first == N2 && dist == 4 && rnk card == Ace)

  in all (inPlace first) zipped

isFlush : Vect 5 Card -> Bool
--isFlush Nil = False
isFlush (card :: cards) = all (((==) `on` suit) card) cards


-- Utils ----------------------------------------------------------

-- rank of the first card in a list
rankOfFirst : Vect (S k) Card -> Rank
rankOfFirst = rnk . head

-- highest rank in a straight (assumes the list is sorted)
straightRank : Vect 5 Card -> Rank
straightRank cards = case lowest of
    N2  => if highest == Ace then secondHighest else highest
    _   => highest

  where
    highest, lowest, secondHighest : Rank
    highest       = rnk $ last cards 
    lowest        = rnk $ head cards
    secondHighest = rnk $ last (init cards)




{-  Find the best pattern in a set of cards and return the pattern with the
    list of cards used in it
-}
bestPatternAndCardsUsed : Vect (S n) Card -> (Pattern, List Card)
bestPatternAndCardsUsed cards = do


  -- Straight, Flush ------------------------------------------------
  let sorted = sortVect cards

  let fiveCardSets = subsequencesOfLengthVect 5 sorted
  
  {-  compare all ranks starting from the strongest 
      (reverse because the card sets are sorted)
  -}
  let cmpFlushes = compare `on` (reverse . map rnk)

  -- compare straight ranks
  let cmpStraights = compare `on` straightRank

  -- sort the straights and flushes so that the best one is first
  let flushes         = sortDescBy cmpFlushes   $ filter isFlush    fiveCardSets
  let straights       = sortDescBy cmpStraights $ filter isStraight fiveCardSets
  let straightFlushes =                           filter isFlush    straights

  let bestFlush : NonEmpty flushes -> Vect 5 Card
      = \prf => head flushes

  let bestStraight : NonEmpty straights -> Vect 5 Card
      = \prf => head straights

  let bestStraightFlush : NonEmpty straightFlushes -> Vect 5 Card
      = \prf => head straightFlushes

  -- N of A Kind ----------------------------------------------------
  let nOfAKinds : List (List Card) = groupByRank (toList cards)
  
  -- compare ranks of the "n-of a kinds" 
  let cmpRanks : {k : Nat} -> Vect (S k) Card -> Vect (S k) Card -> Ordering
      = compare `on` rankOfFirst

  -- sort the "n-of a kinds". to so that the best one is first
  let fourOfAKinds  : List (Vect 4 Card) = sortDescBy cmpRanks $ filterLength 4 nOfAKinds
  let threeOfAKinds : List (Vect 3 Card) = sortDescBy cmpRanks $ filterLength 3 nOfAKinds
  let pairs         : List (Vect 2 Card) = sortDescBy cmpRanks $ filterLength 2 nOfAKinds
  
  let bestFourOfAKind : NonEmpty fourOfAKinds -> Vect 4 Card
      = \prf => head fourOfAKinds
  
  let bestThreeOfAKind : NonEmpty threeOfAKinds -> Vect 3 Card
      = \prf => head threeOfAKinds
  
  let bestPair : NonEmpty pairs -> Vect 2 Card
      = \prf => head pairs
  
  let secondBestPair : ({auto 0 _ : Has 2 pairs} -> Vect 2 Card) = pairs !! 1
  
  let bestHighCard = last sorted
  
  -- choose a pattern -----------------------------------------------

  -- Straight Flush
  let Nil = straightFlushes
      | _ :: _ => ( StraightFlush (straightRank $ bestStraightFlush IsNonEmpty)
                  , toList $ bestStraightFlush IsNonEmpty
                  )
      
  
  -- Four Of A Kind
  let Nil = fourOfAKinds
      | _ :: _ => ( FourOfAKind (rankOfFirst $ bestFourOfAKind IsNonEmpty)
                  , toList $ bestFourOfAKind IsNonEmpty
                  )
  

  {- TODO
  -- Full House
  let (_, _) = (threeOfAKinds, pairs)
      | (_ :: _, _ :: _) => ( FullHouse (rankOfFirst $ bestThreeOfAKind IsNonEmpty)
                                        (rankOfFirst $ bestPair IsNonEmpty)
                            , toList $ bestThreeOfAKind IsNonEmpty ++ bestPair IsNonEmpty
                            )
  -}

  -- Flush
  let Nil = flushes
      | _ :: _ => ( Flush (map rnk $ bestFlush IsNonEmpty)
                  , toList $ bestFlush IsNonEmpty
                  )

  -- Straight
  let Nil = straights
      | _ :: _ => ( Straight (straightRank $ bestStraight IsNonEmpty)
                  , toList $ bestStraight IsNonEmpty
                  )

  
  -- Three Of A Kind
  let Nil = threeOfAKinds
      | _ :: _ => ( ThreeOfAKind (rankOfFirst $ bestThreeOfAKind IsNonEmpty)
                  , toList $ bestThreeOfAKind IsNonEmpty
                  )

  let Nil = pairs
  -- Two Pairs
      | (_ :: _ :: _) =>  ( TwoPairs  (rankOfFirst $ bestPair IsNonEmpty)
                                      (rankOfFirst $ secondBestPair)
                          , toList $ bestPair IsNonEmpty ++ secondBestPair
                          )
  -- Pair
      | (_ :: _) => ( Pair (rankOfFirst $ bestPair IsNonEmpty)
                    , toList $ bestPair IsNonEmpty
                    )
  
  -- High Card
  (HighCard $ rnk bestHighCard, [bestHighCard])


-- Find the best pattern in a set of cards
bestPattern : Vect (S n) Card -> HandWithPattern
bestPattern cards = let

    (ptrn, cardsUsed) = bestPatternAndCardsUsed cards

    -- sort the rest of cards in descending order
    rest : List Card
    rest = sortDescBy compare $ toList cards \\ cardsUsed

  in HandWP { pattern = ptrn, rest = map rnk rest } where

    

-- Rule definitions -----------------------------------------------------------
texasHoldem : Rule n
texasHoldem board hand = bestPattern (board ++ hand)

partial
omahaHoldem : Rule n
omahaHoldem board hand = let
    --fromBoard = filter (ofLength 3) (subsequences $ vecToList board)
    --fromHand  = filter (ofLength 2) (subsequences $ vecToList hand)
    fromBoard = subsequencesOfLengthVect 3 board
    fromHand  = subsequencesOfLengthVect 2 hand

    allCardSets = allConcatsVect fromBoard fromHand

    bestPatterns = map bestPattern allCardSets

  in maximum $ listToList1 bestPatterns

fiveCardDraw : Rule n
--fiveCardDraw _ = bestPattern . vecToList
fiveCardDraw _ = bestPattern


