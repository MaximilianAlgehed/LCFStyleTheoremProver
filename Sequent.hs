{-# LANGUAGE DeriveDataTypeable #-}
module Sequent where

import Prelude hiding (lookup)
import Data.Data
import Data.List hiding (lookup, insert)
import Data.Generics.Uniplate.Data
import Data.Map hiding (map)

import FOL.Abs
import FOL.Par
import FOL.Lex
import FOL.ErrM
import FOL.Print

type Name  = String
data Param = Param Name [Name]
  deriving (Ord, Eq, Show, Data, Typeable)

data Term = Variable   Name
          | Parameter  Param
          | Bound      Int
          | Function   Name [Term]
          deriving (Ord, Eq, Show, Data, Typeable)

data Formula = Predicate      Name  [Term]
             | Connective     Conn  [Formula]
             | Quantification Quant Name Formula
             deriving (Ord, Eq, Show, Data, Typeable)

data Conn = And
          | Or
          | Not
          | Impl
          | Eqv
          deriving (Ord, Eq, Show, Data, Typeable)

data Quant = EX
           | ALL
           deriving (Ord, Eq, Show, Data, Typeable)

data Sequent = [Formula] :|- [Formula]
  deriving (Ord, Eq, Data, Typeable)

parseSequent :: String -> Either String Sequent
parseSequent s = case pSSequent (myLexer s) of 
  Bad s            -> Left s
  Ok (Seq lhs rhs) -> Right $
    (translateForm empty <$> lhs) :|- (translateForm empty <$> rhs)
  where
    translateForm m f = case f of
      FPred (Ident id) ts -> Predicate id    (translateTerm m <$> ts) 
      FNot  f   -> Connective Not  [translateForm m f] 
      FAnd  f g -> Connective And  [translateForm m f, translateForm m g]
      FOr   f g -> Connective Or   [translateForm m f, translateForm m g]
      FImpl f g -> Connective Impl [translateForm m f, translateForm m g]
      FEqv  f g -> Connective Eqv  [translateForm m f, translateForm m g]
      FALL (Ident id) f -> Quantification ALL id (translateForm (extend id m) f)
      FEX  (Ident id) f -> Quantification EX  id (translateForm (extend id m) f)

    translateTerm m t = case t of
      TVar (Ident id)
        | member id m -> let Just i = lookup id m in Bound i
        | otherwise   -> Variable id 
      TParam p              -> Parameter (translateParam p)
      TFunApp (Ident id) ts -> Function id (translateTerm m <$> ts)

    translateParam (PParam (PIdent (Ident id)) ids) =
      Param id [ id | PIdent (Ident id) <- ids ]

    extend id m = insert id 0 ((+1) <$> m)

printSequent :: Sequent -> String
printSequent = printTree . translateSequent 
  where
    translateSequent (lhs :|- rhs) =
      Seq (translateForm empty <$> lhs) (translateForm empty <$> rhs)

    translateForm m f = case f of
      Predicate n ts          -> FPred (Ident n) (translateTerm m <$> ts)
      Connective Not  [t]     -> FNot  (translateForm m t)
      Connective And  [t, t'] -> FAnd  (translateForm m t) (translateForm m t')
      Connective Or   [t, t'] -> FOr   (translateForm m t) (translateForm m t')
      Connective Impl [t, t'] -> FImpl (translateForm m t) (translateForm m t')
      Connective Eqv  [t, t'] -> FEqv  (translateForm m t) (translateForm m t')
      Quantification ALL id t -> FALL (Ident id) (translateForm (extend id m) t)
      Quantification EX  id t -> FEX  (Ident id) (translateForm (extend id m) t)

    translateTerm m t = case t of
      Variable id            -> TVar (Ident id)
      Bound i                -> let Just id = lookup i m in TVar (Ident id)
      Parameter (Param n ns) -> TParam
        (PParam (PIdent $ Ident n) (PIdent . Ident <$> ns))
      Function n ts          -> TFunApp (Ident n) (translateTerm m <$> ts)
    
    extend id m = insert 0 id (mapKeys (+1) m)

instance Show Sequent where
  show = printSequent

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
