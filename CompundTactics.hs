module CompoundTactics where

import Tactics
import Sequent

import Data.List

allBasicLeftTactics :: [Int -> Tactic]
allBasicLeftTactics =
  [ tac_basic
  , tac_allL
  , tac_exL
  , tac_unify
  , tac_conL
  , tac_disjL
  , tac_implL
  , tac_eqvL
  , tac_negL ]

allBasicRightTactics :: [Int -> Tactic]
allBasicRightTactics =
  [ tac_eqlLR
  , tac_eqlRR
  , tac_allR
  , tac_exR
  , tac_unify
  , tac_conR
  , tac_basic
  , tac_disjR
  , tac_implR
  , tac_eqvR
  , tac_negR ]

allSimplifyingRightTactics :: Int -> [Tactic]
allSimplifyingRightTactics i =
  ($i) <$> [ tac_basic
           , tac_conL
           , tac_disjL
           , tac_implL
           , tac_eqvL
           , tac_negL ]

allSimplifyingLeftTactics :: Int -> [Tactic]
allSimplifyingLeftTactics i =
  ($i) <$> [ tac_basic
           , tac_conR
           , tac_disjR
           , tac_implR
           , tac_eqvR
           , tac_negR ]

everywhere :: (Int -> Tactic) -> Tactic
everywhere t ps =
  let n = length $ subGoals ps in
  concat [ t i ps | i <- [0..(n - 1)] ]

simplify :: Int -> Tactic
simplify i ps =
  let resultsR = nub $ concat $ ($ps) <$> allSimplifyingRightTactics i
      resultsL = nub $ concat $ ($ps) <$> allSimplifyingLeftTactics  i
  in
  resultsR ++ resultsL

fully :: Tactic -> Tactic
fully t p = go t [p]
  where
    go t [p]
      | complete p      = [p]
    go t ps
      | null (t <-- ps) = testDone ps
      | otherwise       = go t (testDone $ t <-- ps)

testDone :: [ProofState] -> [ProofState]
testDone ps = if any complete ps then take 1 $ filter complete ps else nub ps

(#) :: Tactic -> Tactic -> Tactic
(#) t t' ps = testDone $ t ps ++ t' ps

infixr #
infixr 1 <--

(<--) :: Tactic -> [ProofState] -> [ProofState]
t <-- ps = testDone $ t =<< ps

auto :: Int -> Tactic
auto fuel p = go fuel [p]
  where
    allTacsEverywhere =
      foldr1 (#)
      (map everywhere (allBasicLeftTactics ++ allBasicRightTactics))

    go 0 ps = ps
    go f ps =
      let tps = allTacsEverywhere <-- ps in
      if null tps then
        testDone ps
      else
        go (f - 1) (testDone tps)
