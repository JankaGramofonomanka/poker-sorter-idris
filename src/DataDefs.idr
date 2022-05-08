module DataDefs

import Data.Vect

import Interfaces

-- Rank -----------------------------------------------------------------------
public export
data Rank
  = N2 | N3 | N4 | N5 | N6 | N7 | N8 | N9 | N10 | Jack | Queen | King | Ace

-- TODO deriving ?
public export
implementation Show Rank where
  show N2     = "N2"
  show N3     = "N3"
  show N4     = "N4"
  show N5     = "N5"
  show N6     = "N6"
  show N7     = "N7"
  show N8     = "N8"
  show N9     = "N9"
  show N10    = "N10"
  show Jack   = "Jack"
  show Queen  = "Queen"
  show King   = "King"
  show Ace    = "Ace"

public export
implementation Eq Rank where
  N2    == N2     = True
  N3    == N3     = True
  N4    == N4     = True
  N5    == N5     = True
  N6    == N6     = True
  N7    == N7     = True
  N8    == N8     = True
  N9    == N9     = True
  N10   == N10    = True
  Jack  == Jack   = True
  Queen == Queen  = True
  King  == King   = True
  Ace   == Ace    = True
  _     == _      = False

public export
implementation Enum Rank where
  fromEnum N2    = 0
  fromEnum N3    = 1
  fromEnum N4    = 2
  fromEnum N5    = 3
  fromEnum N6    = 4
  fromEnum N7    = 5
  fromEnum N8    = 6
  fromEnum N9    = 7
  fromEnum N10   = 8
  fromEnum Jack  = 9
  fromEnum Queen = 10
  fromEnum King  = 11
  fromEnum Ace   = 12

  toEnum 0  = N2
  toEnum 1  = N3
  toEnum 2  = N4
  toEnum 3  = N5
  toEnum 4  = N6
  toEnum 5  = N7
  toEnum 6  = N8
  toEnum 7  = N9
  toEnum 8  = N10
  toEnum 9  = Jack
  toEnum 10 = Queen
  toEnum 11 = King
  toEnum 12 = Ace

public export
implementation Ord Rank where
  compare r1 r2 = compare (fromEnum r1) (fromEnum r2)


-- Suit -----------------------------------------------------------------------
public export
data Suit
  = Heart
  | Diamond
  | Club
  | Spade

public export
implementation Show Suit where
  show Heart    = "Heart"
  show Diamond  = "Diamond"
  show Club     = "Club"
  show Spade    = "Spade"

public export
implementation Eq Suit where
  Heart   == Heart    = True
  Diamond == Diamond  = True
  Club    == Club     = True
  Spade   == Spade    = True
  _       == _        = False


-- Card -----------------------------------------------------------------------
public export
data Card = MkCard Rank Suit

public export
implementation Show Card where
  show (MkCard rank suit) = "MkCard " ++ (show rank) ++ " " ++ (show suit)

public export
implementation Eq Card where
  MkCard rank1 suit1 == MkCard rank2 suit2 = rank1 == rank2 && suit1 == suit2

public export
implementation Ord Card where
  compare (MkCard r1 _) (MkCard r2 _) = compare r1 r2

public export
Board : Type
Board = Vect 5 Card

public export
Hand : Nat -> Type
Hand n = Vect n Card

-- Input ----------------------------------------------------------------------
public export
data GameType = TexasHoldem | OmahaHoldem | FiveCardDraw

implementation Show GameType where
  show TexasHoldem  = "TexasHoldem"
  show OmahaHoldem  = "OmahaHoldem"
  show FiveCardDraw = "FiveCardDraw"

implementation Eq GameType where
  TexasHoldem   == TexasHoldem  = True
  OmahaHoldem   == OmahaHoldem  = True
  FiveCardDraw  == FiveCardDraw = True
  _ == _ = False

public export
data Input : GameType -> Type where
  MkTexasHoldem   : Board ->  List (Hand 2) -> Input TexasHoldem
  MkOmahaHoldem   : Board ->  List (Hand 4) -> Input OmahaHoldem
  MkFiveCardDraw  :           List (Hand 5) -> Input FiveCardDraw

public export
implementation Show (Input t) where
  show (MkTexasHoldem board hands)  = "TexasHoldem " ++ show board ++ " " ++ show hands
  show (MkOmahaHoldem board hands)  = "OmahaHoldem " ++ show board ++ " " ++ show hands
  show (MkFiveCardDraw hands)       = "FiveCardDraw " ++ show hands

public export
implementation Eq (Input t) where

  MkTexasHoldem board1 hands1 == MkTexasHoldem board2 hands2
    = board1 == board2 && hands1 == hands2

  MkOmahaHoldem board1 hands1 == MkOmahaHoldem board2 hands2
    = board1 == board2 && hands1 == hands2

  MkFiveCardDraw hands1       == MkFiveCardDraw hands2
    = hands1 == hands2

public export
data HandsOrd : Nat -> Type where
  MkHandsOrd : List (List (Hand n)) -> HandsOrd n

-- Pattern --------------------------------------------------------------------
public export
data Pattern
  -- `highestRank` - rank of the highest card in the `StraightFlush highestRank`
  = StraightFlush Rank

  -- `rank` - rank of the cards forming the `FourOfAKind rank`
  | FourOfAKind   Rank

  {-  `threeRank` - rank of the cards forming the "three of a kind"
      `pairRank` - rank of the cards forming the "pair"
      in `FullHouse threeRank pairRank`
  -}
  | FullHouse     Rank Rank

  -- `ranks` - ranks of the 5 cards of the same suit in `Flush ranks`
  | Flush         (Vect 5 Rank)

  -- `highestRank` - the highest rank in the sequence in `Straight heighestRank`
  | Straight      Rank

  -- `rank` - the rank of the cards forming the `ThreeOfAKind rank`
  | ThreeOfAKind  Rank

  -- `rank1`, `rank2` - ranks of the 2 pairs in `TwoPairs rank1 rank2`
  | TwoPairs      Rank Rank

  -- `rank` - the rank of the cards forming the "pair" in `Pair rank`
  | Pair          Rank

  -- `rank` the rank of the "high card" in `HighCard rank`
  | HighCard      Rank

public export
implementation Show Pattern where
  show (StraightFlush r    )  = "StraightFlush "  ++ show r
  show (FourOfAKind   r    )  = "FourOfAKind "    ++ show r
  show (FullHouse     r1 r2)  = "FullHouse "      ++ show r1 ++ " " ++ show r2
  show (Flush         rs   )  = "Flush "          ++ show rs
  show (Straight      r    )  = "Straight "       ++ show r
  show (ThreeOfAKind  r    )  = "ThreeOfAKind "   ++ show r
  show (TwoPairs      r1 r2)  = "TwoPairs "       ++ show r1 ++ " " ++ show r2
  show (Pair          r    )  = "Pair "           ++ show r
  show (HighCard      r    )  = "HighCard "       ++ show r

public export
implementation Eq Pattern where
  (StraightFlush rl    )  == (StraightFlush rr    )   = rl == rr
  (FourOfAKind   rl    )  == (FourOfAKind   rr    )   = rl == rr
  (FullHouse     rl1 rl2) == (FullHouse     rr1 rr2)  = rl1 == rr1 && rl2 == rr2
  (Flush         rls   )  == (Flush         rrs   )   = rls == rrs
  (Straight      rl    )  == (Straight      rr    )   = rl == rr
  (ThreeOfAKind  rl    )  == (ThreeOfAKind  rr    )   = rl == rr
  (TwoPairs      rl1 rl2) == (TwoPairs      rr1 rr2)  = rl1 == rr1 && rl2 == rr2
  (Pair          rl    )  == (Pair          rr    )   = rl == rr
  (HighCard      rl    )  == (HighCard      rr    )   = rl == rr
  _ == _ = True


