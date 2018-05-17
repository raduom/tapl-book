{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE PartialTypeSignatures #-}
module Untyped.Arithmetic where

import           Data.Functor.Foldable      (Fix (..), unfix)

-- Parsing
import           Control.Monad              (void)
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Expr

data Term a = TmTrue
            | TmFalse
            | TmIf a a a
            | TmZero
            | TmSucc a
            | TmPred a
            | TmIsZero a
            deriving (Eq, Show, Functor)

isNumeric :: Fix Term -> Bool
isNumeric (Fix TmZero)     = True
isNumeric (Fix (TmSucc r)) = isNumeric r
isNumeric _                = False

isValue :: Fix Term -> Bool
isValue (Fix TmTrue)  = True
isValue (Fix TmFalse) = True
isValue t             | isNumeric t = True
isValue _             = False

eval1 :: Fix Term -> Fix Term
eval1 (Fix (TmIf (Fix TmTrue) t  _))     = t
eval1 (Fix (TmIf (Fix TmFalse) _ t))     = t
eval1 (Fix (TmIf t1 t2 t3))              = Fix (TmIf (eval1 t1) t2 t3)
eval1 (Fix (TmSucc t1))                  = Fix (TmSucc (eval1 t1))
eval1 (Fix (TmPred (Fix TmZero)))        = Fix TmZero
eval1 (Fix (TmPred (Fix (TmSucc nv))))   | isNumeric nv = nv
eval1 (Fix (TmPred t))                   = Fix (TmPred (eval1 t))
eval1 (Fix (TmIsZero (Fix TmZero)))      = Fix TmTrue
eval1 (Fix (TmIsZero (Fix (TmSucc nv)))) | isNumeric nv = Fix TmFalse
eval1 (Fix (TmIsZero t))                 = Fix (TmIsZero (eval1 t))
eval1 t                                  = t -- Term can no longer be reduced.

{-
I will defined the function myself for now, until I get used to the
idea, then I will use the function from recursion-schemes.

1. Unpack the Fix so we get access to the children.
2. Apply the bottomUp fn recursively for each child of the term.
3. Repack the term into a Fix.
4. Apply the function to the repacked Fix.
-}

bottomUp :: Functor a => (Fix a -> Fix a) -> Fix a -> Fix a
bottomUp fn = fn . Fix . fmap (bottomUp fn) . unfix

{- Evaluate AST, same name as in the book -}
eval :: Fix Term -> Fix Term
eval = bottomUp eval1

{-
4.2.2
Change the definition of the eval function in the arith implementation to
the big-step style introduced in ex. 3.5.17
-}

eval2 :: Fix Term -> Fix Term
eval2 (Fix (TmIf t1 t2 t3)) =
  case eval2 t1 of
    Fix TmTrue -> eval2 t2
    _          -> eval2 t3
eval2 (Fix (TmSucc t1)) = Fix (TmSucc (eval2 t1))
eval2 (Fix (TmPred t)) =
  case eval2 t of
    Fix TmZero      -> Fix TmZero
    Fix (TmSucc nv) -> Fix (TmSucc nv)
    _               -> undefined -- Not defined for boolean values
eval2 (Fix (TmIsZero (Fix TmZero))) = Fix TmTrue
eval2 (Fix (TmIsZero (Fix (TmSucc nv)))) | isNumeric nv = Fix TmFalse
eval2 (Fix (TmIsZero t)) =
  case eval2 t of
    Fix TmZero      -> Fix TmTrue
    Fix (TmSucc nv) -> Fix TmFalse
    _               -> undefined -- Not defined for boolean values
eval2 t | isValue t = t -- Term can no longer be reduced.
eval2 _ = undefined

{- Lexer -}

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

reservedWord :: String -> Parser ()
reservedWord w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

{- Parser -}

expr :: Parser (Fix Term)
expr = ifExpr
   <|> succExpr
   <|> predExpr
   <|> isZeroExpr
   <|> zeroExpr
   <|> trueExpr
   <|> falseExpr
   <|> parens expr

ifExpr :: Parser (Fix Term)
ifExpr = do
  reservedWord "if"
  condition <- expr
  reservedWord "then"
  thenExpr <- expr
  reservedWord "else"
  elseExpr <- expr
  return (Fix (TmIf condition thenExpr elseExpr))

succExpr :: Parser (Fix Term)
succExpr = do
  reservedWord "succ"
  nv <- expr
  return (Fix (TmSucc nv))

predExpr :: Parser (Fix Term)
predExpr = do
  reservedWord "pred"
  nv <- expr
  return (Fix (TmPred nv))

isZeroExpr :: Parser (Fix Term)
isZeroExpr = do
  reservedWord "iszero"
  nv <- expr
  return (Fix (TmIsZero nv))

trueExpr :: Parser (Fix Term)
trueExpr = do
  reservedWord "true"
  return (Fix TmTrue)

falseExpr :: Parser (Fix Term)
falseExpr = do
  reservedWord "false"
  return (Fix TmFalse)

zeroExpr :: Parser (Fix Term)
zeroExpr = do
  reservedWord "0"
  return (Fix TmZero)
