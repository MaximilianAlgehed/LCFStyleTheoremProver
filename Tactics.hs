{-# LANGUAGE DeriveDataTypeable #-}
module Tactics where

import Data.Data

import Sequent

data ProofState =
  ProofState { finalGoal :: Sequent
             , subGoals  :: [Sequent]
             , freeVar   :: Int
             } deriving (Ord, Eq, Data, Typeable)

instance Show ProofState where
  show ps
    | complete ps =
      show (finalGoal ps) ++ "\nProved!" ++
      "\n--------------------------------\n"
    | otherwise =
      "final goal:\n " ++ show (finalGoal ps) ++ "\n\n" ++
      "subgoals:\n" ++
      unlines [ show n ++ ". " ++ show s
              | (n, s) <- zip [0..] (subGoals ps)] ++
      "\n--------------------------------\n"

type Tactic = ProofState -> [ProofState]

initial :: Sequent -> ProofState
initial s = ProofState { finalGoal = s
                       , subGoals  = [s]
                       , freeVar   = 0 }

complete :: ProofState -> Bool
complete = null . subGoals

gensym :: Int -> String
gensym n
  | n < 26    = letter n
  | otherwise = gensym (n `div` 26) ++ letter (n `mod` 26)
  where
    letter :: Int -> String
    letter n = (:[]) $ ['a'..'z'] !! n

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

splitQuantifier :: Quant -> [Formula] -> [(Formula, String, [Formula])]
splitQuantifier q []     = []
splitQuantifier q (f:fs) =
  case f of
    Quantification q' n fs'
      | q' == q -> (fs', n, fs) :
                   fmap (\(f', s, fs) -> (f', s, f:fs)) (splitQuantifier q fs)
    _ -> fmap (\(f', s, fs) -> (f', s, f:fs)) (splitQuantifier q fs)

replaceAt :: [Formula] -> Int -> Term -> Term -> [Formula]
replaceAt fs i t u =
  take (i - 1) fs ++ [replace t u (fs !! i)] ++ drop (i + 1) fs

makeFresh :: String -> ProofState -> String 
makeFresh n ps = let sym = gensym (freeVar ps) in
  if sym `elem` variables ps then
    makeFresh (n ++ sym) ps
  else
    n ++ sym

tac_cut :: Int -> String -> Tactic
tac_cut i f ps =
  case parseFormula f of
    Right f -> let (lhs :|- rhs) = subGoals ps !! i in
               [ spliceGoals ps i [ lhs |- [f], (f:lhs) |- rhs] ]
    _ -> []

tac_eqlL :: Int -> String -> Tactic
tac_eqlL i t ps =
  case parseTerm t of
    Right t -> let (lhs :|- rhs) = subGoals ps !! i in
               [ spliceGoals ps i [ (Equality t t : lhs) |- rhs ] ]
    _ -> []

tac_eqlLR :: Int -> Tactic
tac_eqlLR i ps =
  let (lhs :|- rhs) = subGoals ps !! i in
    filter (/= ps) $
    concat
      [ [ spliceGoals ps i [ lhs |- (replaceAt rhs n t u) ]
        | n <- [0..length rhs - 1] ]
      | Equality t u <- lhs ]

tac_eqlRR :: Int -> Tactic
tac_eqlRR i ps =
  let (lhs :|- rhs) = subGoals ps !! i in
    filter (/= ps) $
    concat
      [ [ spliceGoals ps i [ lhs :|- (replaceAt rhs n t u) ]
        | n <- [0..length rhs - 1] ]
      | Equality u t <- lhs ]

tac_allL :: Int -> Tactic
tac_allL i ps =
  let (lhs :|- rhs) = subGoals ps !! i
      fv = freeVar ps 
      fresh n = makeFresh n ps
  in [ (spliceGoals ps i [(substitute 0 (Variable $ fresh n) f : lhs) |- rhs])
       { freeVar = fv + 1 }
     | (f, n, _) <- splitQuantifier ALL lhs ]

tac_allR :: Int -> Tactic
tac_allR i ps =
  let (lhs :|- rhs) = subGoals ps !! i
      vars          = variables $ subGoals ps !! i
      fv            = freeVar ps
      fresh n = makeFresh n ps
  in [ (spliceGoals ps i
        [lhs |- (substitute 0 (Parameter (Param (fresh n) vars)) f : rhs')])
       { freeVar = fv + 1 }
     | (f, n, rhs') <- splitQuantifier ALL rhs ]

tac_exL :: Int -> Tactic
tac_exL i ps =
  let (lhs :|- rhs) = subGoals ps !! i
      vars          = variables $ subGoals ps !! i
      fv            = freeVar ps
      fresh n = makeFresh n ps
  in [ (spliceGoals ps i
        [(substitute 0 (Parameter (Param (fresh n) vars)) f : lhs') |- rhs])
       { freeVar = fv + 1 }
     | (f, n, lhs') <- splitQuantifier EX lhs ]

tac_exR :: Int -> Tactic
tac_exR i ps =
  let (lhs :|- rhs) = subGoals ps !! i
      fv = freeVar ps 
      fresh n = makeFresh n ps
      vars    = variables (subGoals ps !! i)
  in [ (spliceGoals ps i
        [lhs |- (substitute 0 (Parameter (Param (fresh n) vars)) f : rhs)])
       { freeVar = fv + 1 }
     | (f, n, _) <- splitQuantifier EX rhs ]

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
  in [ spliceGoals ps i [ (a:b:lhs') |- rhs ]
     | ([a, b], lhs') <- splitConnective And lhs ]

tac_conR :: Int -> Tactic
tac_conR i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ lhs |- (a:rhs'), lhs |- (b:rhs') ]
     | ([a, b], rhs') <- splitConnective And rhs ]

tac_disjL :: Int -> Tactic
tac_disjL i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ (a:lhs') |- rhs, (b:lhs') |- rhs ]
     | ([a, b], lhs') <- splitConnective Or lhs ]

tac_disjR :: Int -> Tactic
tac_disjR i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ lhs |- (a:b:rhs') ]
     | ([a, b], rhs') <- splitConnective Or rhs ]

tac_implL :: Int -> Tactic
tac_implL i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ lhs' |- (a:rhs), (b:lhs') |- rhs ]
     | ([a, b], lhs') <- splitConnective Impl lhs ]

tac_implR :: Int -> Tactic
tac_implR i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ (a:lhs) |- (b:rhs') ]
     | ([a, b], rhs') <- splitConnective Impl rhs ]

tac_eqvL :: Int -> Tactic
tac_eqvL i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ (a:b:lhs') |- rhs, lhs' |- (a:b:rhs) ]
     | ([a, b], lhs') <- splitConnective Eqv lhs ]

tac_eqvR :: Int -> Tactic
tac_eqvR i ps =
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ (a:lhs) |- (b:rhs'), (b:lhs) |- (a:rhs') ]
     | ([a, b], rhs') <- splitConnective Eqv rhs ]

tac_negL :: Int -> Tactic
tac_negL i ps = 
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ lhs' |- (a:rhs)]
     | ([a], lhs') <- splitConnective Not lhs ]

tac_negR :: Int -> Tactic
tac_negR i ps = 
  let (lhs :|- rhs) = subGoals ps !! i
  in [ spliceGoals ps i [ (a:lhs) |- rhs']
     | ([a], rhs') <- splitConnective Not rhs ]
