module CompoundTactics where

import Tactics
import Sequent

import Data.List

simplify :: Int -> Tactic
simplify i ps =
  let resultsR = nub $ concat $ ($ps) <$> allBasicRightTactics i
      resultsL = nub $ concat $ ($ps) <$> allBasicLeftTactics  i
  in
  nub $ resultsR ++ resultsL
