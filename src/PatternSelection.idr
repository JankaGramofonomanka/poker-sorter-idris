module PatternSelection

import Data.List
import Data.List1
import Data.Vect

import Interfaces
import DataDefs
import HandOrder
import Utils


{-  `Rule` is a type of functions that represent poker rules. A function of 
    type `Rule` selects the best pattern from a hand and a board (optionally)
    according to the rule it represents.
-}
public export
Rule : GameType -> Type
Rule TexasHoldem  = Board ->  Hand (handSize TexasHoldem)   -> HandWithPattern
Rule OmahaHoldem  = Board ->  Hand (handSize OmahaHoldem)   -> HandWithPattern
Rule FiveCardDraw =           Hand (handSize FiveCardDraw)  -> HandWithPattern

-- Helper functions -----------------------------------------------------------
rnk : Card -> Rank
rnk (MkCard r _) = r

suit : Card -> Suit
suit (MkCard _ s) = s


groupByRank : List Card -> List (List Card)
groupByRank l = map list1ToList $ (groupBy ((==) `on` rnk) . sort) l


isStraight : Vect 5 Card -> Bool
isStraight cards = let

    sorted = sortVect cards
    (first :: rest) = sorted

    nats : Vect 4 Nat
    nats = [1, 2, 3, 4]

    zipped : Vect 4 (Nat, Card)
    zipped = zip nats rest

    inPlace : Card -> (Nat, Card) -> Bool
    inPlace first (dist, card)
      =   rankNum (rnk first) + dist == rankNum (rnk card)
      ||  (rnk first == N2 && dist == 4 && rnk card == Ace)

  in all (inPlace first) zipped

isFlush : Vect 5 Card -> Bool
isFlush (card :: cards) = all (((==) `on` suit) card) cards

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

{-  compare all ranks starting from the strongest 
    (reverse because the card sets are sorted)
-}
cmpFlushes : Vect 5 Card -> Vect 5 Card -> Ordering
cmpFlushes = compare `on` (reverse . map rnk)

-- compare straight ranks
cmpStraights : Vect 5 Card -> Vect 5 Card -> Ordering
cmpStraights = compare `on` straightRank

-- compare ranks of the "n-of a kinds" 
cmpRanks : Vect (S k) Card -> Vect (S k) Card -> Ordering
cmpRanks = compare `on` rankOfFirst

bothNonEmpty : (l1 : List a) -> (l2 : List b) -> Maybe (NonEmpty l1, NonEmpty l2)
bothNonEmpty (_ :: _) (_ :: _) = Just (IsNonEmpty, IsNonEmpty)
bothNonEmpty _ _ = Nothing




{-  Find the best pattern in a set of cards and return the pattern with the
    list of cards used in it
-}
bestPatternAndCardsUsed : Vect (S n) Card -> (Pattern, List Card)
bestPatternAndCardsUsed cards = do


  -- Straight, Flush ------------------------------------------------
  let sorted = sortVect cards

  let fiveCardSets = subsequencesOfLengthVect 5 sorted
  
  -- sort the straights and flushes so that the best one is first
  let flushes         = sortDescBy cmpFlushes   $ filter isFlush    fiveCardSets
  let straights       = sortDescBy cmpStraights $ filter isStraight fiveCardSets
  let straightFlushes =                           filter isFlush    straights

  let bestFlush         : {auto 0 _ : NonEmpty flushes}         -> Vect 5 Card
      = head flushes

  let bestStraight      : {auto 0 _ : NonEmpty straights}       -> Vect 5 Card
      = head straights

  let bestStraightFlush : {auto 0 _ : NonEmpty straightFlushes} -> Vect 5 Card
      = head straightFlushes

  -- N of A Kind ----------------------------------------------------
  let nOfAKinds : List (List Card) = groupByRank (toList cards)

  -- sort the "n-of a kinds", to so that the best one is first
  let fourOfAKinds  : List (Vect 4 Card) = sortDescBy cmpRanks $ filterLength 4 nOfAKinds
  let threeOfAKinds : List (Vect 3 Card) = sortDescBy cmpRanks $ filterLength 3 nOfAKinds
  let pairs         : List (Vect 2 Card) = sortDescBy cmpRanks $ filterLength 2 nOfAKinds
  
  let bestFourOfAKind   : {auto 0 _ : NonEmpty fourOfAKinds}  -> Vect 4 Card
      = head fourOfAKinds
  
  let bestThreeOfAKind  : {auto 0 _ : NonEmpty threeOfAKinds} -> Vect 3 Card
      = head threeOfAKinds
  
  let bestPair          : {auto 0 _ : NonEmpty pairs}         -> Vect 2 Card
      = head pairs
  
  let secondBestPair    : {auto 0 _ : Has 2 pairs}            -> Vect 2 Card
      = pairs !! 1
  
  let bestHighCard = last sorted
  
  -- choose a pattern -----------------------------------------------

  -- Straight Flush
  let Nil = straightFlushes
      | _ :: _ => ( StraightFlush (straightRank bestStraightFlush)
                  , toList bestStraightFlush
                  )
  
  -- Four Of A Kind
  let Nil = fourOfAKinds
      | _ :: _ => ( FourOfAKind (rankOfFirst $ bestFourOfAKind)
                  , toList $ bestFourOfAKind
                  )
  
  -- TODO find a prettier way than using `bothNonEmpty`
  -- Full House
  let Nothing = bothNonEmpty threeOfAKinds pairs
      | Just (prf3, prf2) =>  ( FullHouse (rankOfFirst $ bestThreeOfAKind)
                                          (rankOfFirst $ bestPair)
                              , toList $ bestThreeOfAKind ++ bestPair
                              )

  -- Flush
  let Nil = flushes
      | _ :: _ => ( Flush (map rnk bestFlush)
                  , toList $ bestFlush
                  )

  -- Straight
  let Nil = straights
      | _ :: _ => ( Straight (straightRank bestStraight)
                  , toList $ bestStraight
                  )

  -- Three Of A Kind
  let Nil = threeOfAKinds
      | _ :: _ => ( ThreeOfAKind (rankOfFirst $ bestThreeOfAKind)
                  , toList $ bestThreeOfAKind
                  )

  let Nil = pairs
  -- Two Pairs
      | (_ :: _ :: _) =>  ( TwoPairs  (rankOfFirst $ bestPair)
                                      (rankOfFirst $ secondBestPair)
                          , toList $ bestPair ++ secondBestPair
                          )

  -- Pair
      | (_ :: _) => ( Pair (rankOfFirst $ bestPair)
                    , toList $ bestPair
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
public export
texasHoldem : Rule TexasHoldem
texasHoldem board hand = bestPattern (board ++ hand)

public export
partial
omahaHoldem : Rule OmahaHoldem
omahaHoldem board hand = let
    fromBoard = subsequencesOfLengthVect 3 board
    fromHand  = subsequencesOfLengthVect 2 hand

    allCardSets = allConcatsVect fromBoard fromHand

    bestPatterns = map bestPattern allCardSets

  in maximum $ listToList1 bestPatterns

public export
fiveCardDraw : Rule FiveCardDraw
fiveCardDraw = bestPattern


