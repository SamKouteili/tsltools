{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      :  TSL.ModuloTheories.Nra
-- Description :  Nonlinear Real Arithmetic
-- Maintainer  :  Sam Kouteili
module TSL.ModuloTheories.Theories.Nra (NraSymbol) where

import TSL.ModuloTheories.Theories.Base (TheorySymbol (..))
import Text.Regex.PCRE.Heavy (re, scan)

data NraSymbol
  = Real Double
  | Var String
  | Add
  | Sub
  | Mult
  | Div
  | Eq
  | Gt
  | Lt
  | Gte
  | Lte
  deriving (Eq, Ord)

instance TheorySymbol NraSymbol where
  readT = \case
    "add" -> Right Add
    "sub" -> Right Sub
    "mult" -> Right Mult
    "div" -> Right Div
    "eq" -> Right Eq
    "gt" -> Right Gt
    "lt" -> Right Lt
    "gte" -> Right Gte
    "lte" -> Right Lte
    value -> case scan [re|real(Neg)?([0-9]*\.?[0-9]+)|] value of
      [(_, [neg, num])] ->
        let r = read num :: Double
         in Right $ Real $ if neg == "Neg" then negate r else r
      _ -> case scan [re|int(Neg)?([0-9]+)|] value of
        [(_, [neg, num])] ->
          let r = read num :: Double
           in Right $ Real $ if neg == "Neg" then negate r else r
        _ -> Right $ Var value

  toSmt = \case
    (Real r) -> show r
    (Var v) -> v
    Add -> "+"
    Sub -> "-"
    Mult -> "*"
    Div -> "/"
    Eq -> "="
    Gt -> ">"
    Lt -> "<"
    Gte -> ">="
    Lte -> "<="

  toTsl = \case
    (Real r) ->
      if r < 0
        then "realNeg" ++ show (abs r) ++ "()"
        else "real" ++ show r ++ "()"
    (Var v) -> v
    Add -> "add"
    Sub -> "sub"
    Mult -> "mult"
    Div -> "div"
    Eq -> "eq"
    Gt -> "gt"
    Lt -> "lt"
    Gte -> "gte"
    Lte -> "lte"

  symbolType _ = "Real"
  isUninterpreted _ = False
  makeSignal = Var
