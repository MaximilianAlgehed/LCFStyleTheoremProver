{-# LANGUAGE DeriveDataTypeable #-}
module Sequent where

import Prelude hiding (lookup)
import Data.Data
import Data.List hiding (lookup, insert)
import Data.Generics.Uniplate.Data
import Data.Map hiding (map)
import qualified Data.Map as M

import Control.Monad
import Control.Monad.Except

import FOL.Abs
import FOL.Par
import FOL.Lex
import FOL.ErrM
import FOL.Print

type Name  = String

data Param = Param Name [Name]
  deriving (Ord, Eq, Data, Typeable)

instance Show Param where
  show (Param n ns) = n ++ "<" ++ intercalate ", " (("?"++) <$> ns) ++ ">"

data Term = Variable    Name
          | SynVariable Name -- Only exists during pretty printing
          | Parameter   Param
          | Bound       Int
          | Function    Name [Term]
          deriving (Ord, Eq, Data, Typeable)

instance Show Term where
  show t = case t of
    Variable n    -> "?" ++ n
    SynVariable n -> n
    Parameter p   -> show p
    Function f ts -> f ++ "(" ++ intercalate ", " (show <$> ts) ++ ")"

data Formula = Predicate      Name  [Term]
             | Connective     Conn  [Formula]
             | Quantification Quant Name Formula
             deriving (Ord, Eq, Data, Typeable)

instance Show Formula where
  showsPrec p f = case f of
    Predicate n ts ->
      showParen (p > 5) $ showString
        (n ++ "(" ++ intercalate ", " (show <$> ts) ++ ")")
    Connective Not [f] ->
      showParen (p > 5) $ showString "~" . showsPrec 5 f
    Connective c [l, r] ->
      let prec = precedence c in
      showParen (p > prec) $
        showsPrec (prec + 1) l .
        showString (" " ++ show c ++ " ") .
        showsPrec prec r
    Quantification q n f ->
      showParen (p > 0) $
        showString (show q ++ " " ++ n ++ ". " ++
                    show (substitute 0 (SynVariable n) f))

data Conn = And
          | Or
          | Not
          | Impl
          | Eqv
          deriving (Ord, Eq, Data, Typeable)

precedence :: Conn -> Int
precedence c = case c of
  And  -> 4
  Or   -> 3
  Not  -> 5
  Impl -> 2
  Eqv  -> 1

instance Show Conn where
  show c = case c of
    And  -> "&"
    Or   -> "|"
    Impl -> "->"
    Eqv  -> "="
    Not  -> "~"

data Quant = EX
           | ALL
           deriving (Ord, Eq, Data, Typeable)

instance Show Quant where
  show EX  = "EX"
  show ALL = "ALL"

data Sequent = [Formula] :|- [Formula]
  deriving (Ord, Eq, Data, Typeable)

instance Show Sequent where
  show (lhs :|- rhs) =
    intercalate ", " (show <$> lhs) ++ " |- " ++ intercalate ", " (show <$> rhs)

parseSequent :: String -> Either String Sequent
parseSequent s = case pSSequent (myLexer s) of 
  Bad s            -> Left s
  Ok (Seq lhs rhs) -> Right $
    (translateForm empty <$> lhs) :|- (translateForm empty <$> rhs)
  where
    translateForm m f = case f of
      FPred (Ident id) ts -> Predicate id (translateTerm m <$> ts) 
      FNot  f   -> Connective Not  [translateForm m f] 
      FAnd  f g -> Connective And  [translateForm m f, translateForm m g]
      FOr   f g -> Connective Or   [translateForm m f, translateForm m g]
      FImpl f g -> Connective Impl [translateForm m f, translateForm m g]
      FEqv  f g -> Connective Eqv  [translateForm m f, translateForm m g]
      FALL (Ident id) f -> Quantification ALL id (translateForm (extend id m) f)
      FEX  (Ident id) f -> Quantification EX  id (translateForm (extend id m) f)

    translateTerm m t = case t of
      TVar (Ident id)
        | otherwise   -> Variable id 
      TBVar (Ident id)
        | member id m -> let Just i = lookup id m in Bound i
        | otherwise   -> Variable id
      TParam p              -> Parameter (translateParam p)
      TFunApp (Ident id) ts -> Function id (translateTerm m <$> ts)

    translateParam (PParam (Ident id) ids) =
      Param id [ id | PIdent (Ident id) <- ids ]

    extend id m = insert id 0 ((+1) <$> m)

sequent :: String -> Sequent
sequent s = case parseSequent s of
  Left e  -> error e
  Right s -> s

(|-) :: [Formula] -> [Formula] -> Sequent
(|-) = (:|-)

replace :: Term -> Term -> Term -> Term 
replace u1 u2 = rewrite go
  where
    go t = if t == u1 then Just u2 else Nothing

abstract :: Int -> Term -> Formula -> Formula
abstract i t f = case f of
  Predicate n ts       -> Predicate n (map (replace t (Bound i)) ts)
  Connective c fs      -> Connective c (map (abstract i t) fs)
  Quantification q n f -> Quantification q n (abstract (i + 1) t f)

substitute :: Int -> Term -> Formula -> Formula
substitute i t f = case f of
  Predicate n ts       -> Predicate n (map (replace (Bound i) t) ts)
  Connective c fs      -> Connective c (map (substitute i t) fs)
  Quantification q n f -> Quantification q n (substitute (i + 1) t f)

variables :: Data t => t -> [Name]
variables a = nub [ n | Variable n <- universeBi a ]

parameters :: Data t => t -> [Param]
parameters = nub . universeBi

type Env = Map Name Term

unify :: Env -> Term -> Term -> Either String Env
unify env tin uin = let (t, u) = (apply env tin, apply env uin) in
  case (t, u) of
    (Variable a, u)
      | t == u                 -> return env
      | occurs a (apply env u) -> throwError "Occurs check failed"
      | otherwise              -> return $ insert a u env
    (_, Variable a)            -> unify env u t
    (Parameter (Param a _), Parameter (Param b _))
      | a == b    -> return env
      | otherwise -> throwError "Can not unify different parameters"
    (Function a ts, Function b us)
      | a == b    -> foldM (uncurry . unify) env (zip ts us)
      | otherwise -> throwError "Can not unify different functions"
    _ -> throwError "Unable to unify terms"

atoms :: Formula -> Formula -> Either String Env
atoms (Predicate a ts) (Predicate b us) = do
  unless (a == b) $ throwError "Cannot unify different predicates"
  foldM (uncurry . unify) empty (zip ts us)
atoms _ _ = throwError "Expected predicates"

apply :: Data t => Env -> t -> t 
apply env = rewriteBi go
  where
    go (Variable n) = lookup n env
    go _            = Nothing

occurs :: Name -> Term -> Bool
occurs n t =
  elem n (variables t) ||
  elem n (concat [ vs | Param _ vs <- parameters t ])
