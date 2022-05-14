module Lib

import Data.List
import Data.List1

import DataDefs
import PatternSelection
import HandOrder


--  Sort poker hands according to a poker rule.
sortHands : (Hand n -> HandWithPattern) -> List (Hand n) -> HandsOrd n
sortHands bestPtrn hands = let

  -- sort according to the best possible pattern
  sorted : List (Hand n)
  sorted = sortBy (compare `on` bestPtrn) hands

  -- group hands with equivalent best pattern
  sortedAndGrouped : List (List1 (Hand n))
  sortedAndGrouped = groupBy ((==) `on` bestPtrn) sorted

  in MkHandsOrd sortedAndGrouped

public export
partial
process : Input game -> HandsOrd (handSize game)
process input = case input of
  MkTexasHoldem board hands => sortHands (texasHoldem board) hands
  MkOmahaHoldem board hands => sortHands (omahaHoldem board) hands
  MkFiveCardDraw      hands => sortHands fiveCardDraw hands




