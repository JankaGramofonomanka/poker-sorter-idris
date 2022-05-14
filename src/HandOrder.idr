module HandOrder

import Data.List
import Data.Vect

import DataDefs
import Interfaces
import Utils

public export
record HandWithPattern where
  constructor HandWP
  pattern : Pattern
  rest : List Rank

public export
implementation Show HandWithPattern where
  show (HandWP { pattern = pattern, rest = rest })
    = "HandWP { pattern = " ++ show pattern ++ ", rest = " ++ show rest ++ " }"

public export
implementation Eq HandWithPattern where
  HandWP { pattern = p1, rest = r1 } == HandWP { pattern = p2, rest = r2 }
    = p1 == p2 && r1 == r2


public export
rankNum : Rank -> Nat
rankNum = finToNat . fromEnum

{-  assign a number to each pattern type so that the stronger the pattern, 
    the bigger the number, ignoring ranks of the cards forming a pattern.
    
    For example a straight will be stronger than a pair, but two pairs will
    always be equal even if one has a higher rank.
-}
public export
patternTypeNum : Pattern -> Nat
patternTypeNum p = case p of

  StraightFlush _   => 8
  FourOfAKind   _   => 7
  FullHouse     _ _ => 6
  Flush         _   => 5
  Straight      _   => 4
  ThreeOfAKind  _   => 3
  TwoPairs      _ _ => 2
  Pair          _   => 1
  HighCard      _   => 0

{-  assign a list of numbers to a pattrern so that the first number is the 
    pattern type number (see `patternTypeNum`) and the next number is a number 
    based on which the order between the patterns will be determined if the 
    type numbers are equal. If the second numbers are equal, then the third will 
    be used etc.
-}
public export
patternNumList : Pattern -> List Nat
patternNumList p = patternTypeNum p :: patternContentNums where

  patternContentRanks : List Rank
  patternContentRanks = case p of
    StraightFlush highestRank         => [ highestRank ]
    FourOfAKind   rank                => [ rank ]
    FullHouse     threeRank pairRank  => [ threeRank, pairRank ]
    Flush         ranks               => sortDesc (toList ranks)
    Straight      highestRank         => [ highestRank ]
    ThreeOfAKind  rank                => [ rank ]
    TwoPairs      rank1 rank2         => sortDesc [ rank1, rank2 ]
    Pair          rank                => [ rank ]
    HighCard      rank                => [ rank ]
  
  patternContentNums : List Nat
  patternContentNums = map rankNum patternContentRanks


{-  just like `patternNumList`, but taking into account the rest of the cards a 
    player has in his hand or on the board.
-}

public export
handNumList : HandWithPattern -> List Nat
handNumList (HandWP { pattern, rest })
  = patternNumList pattern ++ map rankNum (sortDesc rest)

public export
implementation Ord Pattern where
  compare = compare `on` patternNumList

public export
implementation Ord HandWithPattern where
  compare = compare `on` handNumList



