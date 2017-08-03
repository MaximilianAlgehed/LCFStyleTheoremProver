{-# LANGUAGE DeriveDataTypeable #-}
module Tactics where

import Data.Data

import Sequent

data ProofState =
  ProofState { finalGoal :: Sequent
             , subGoals  :: [Sequent]
             } deriving (Ord, Eq, Data, Typeable, Show)

type Tactic = ProofState -> [ProofState]

initial :: Sequent -> ProofState
initial s = ProofState { finalGoal = s
                       , subGoals  = [s] }

spliceGoals :: ProofState -> Int -> [Sequent] -> ProofState
spliceGoals ps i gls =
  let sgs = subGoals ps in
  ps { subGoals = take i sgs ++ gls ++ drop (i + 1) sgs }

splitConnective :: Conn -> [Formula] -> [([Formula], [Formula])]
splitConnective c []     = []
splitConnective c (f:fs) =
  case f of
    Connective c' fs'
      | c' == c -> (fs', fs) : fmap (fmap (f:)) (splitConnective c fs)
    _ -> fmap (fmap (f:)) (splitConnective c fs)

tac_basic :: Int -> Tactic
tac_basic i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in if or [ or [ l == r | r <- rhs ] | l <- lhs ]
     then [spliceGoals ps i []]
     else []

tac_unify :: Int -> Tactic
tac_unify i ps =
  let (lhs :|- rhs) = subGoals ps !! i
      unifiable = [ env | Right env <- concat [ atoms l <$> rhs | l <- lhs ] ]
  in [ apply env (spliceGoals ps i []) | env <- unifiable ]

tac_conL :: Int -> Tactic
tac_conL i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ (a:b:lhs') :|- rhs ]
     | ([a, b], lhs') <- splitConnective And lhs ]

tac_conR :: Int -> Tactic
tac_conR i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ lhs :|- (a:rhs'), lhs :|- (b:rhs') ]
     | ([a, b], rhs') <- splitConnective And rhs ]
