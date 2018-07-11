{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE OverloadedStrings #-}

module Typed.Simple.Parser where

import           Control.Monad                    (void)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.State.Strict (State, evalState, get, modify)
import           Data.Functor.Foldable            (Fix (..))
import           Data.List                        (elemIndex)
import           Data.Maybe                       (fromJust)
import qualified Data.Text                        as T (Text, pack)
import           Data.Void                        (Void)
import           Text.Megaparsec                  (ParsecT, between, empty, many, runParserT, (<|>))
import           Text.Megaparsec.Char             (char, letterChar, space1)
import qualified Text.Megaparsec.Char.Lexer       as L (lexeme, space, symbol)
import           Text.Megaparsec.Expr             (Operator (..), makeExprParser)

import           Typed.Simple.Syntax

{- Lexer -}

type Parser = ParsecT Void T.Text (State VarContext)

type VarContext = [T.Text]

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: T.Text -> Parser T.Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

identifier :: Parser T.Text
identifier =
  T.pack <$> ((:) <$> letterChar <*> many (char '\''))

tyTerm :: Parser Type
tyTerm = parens tyExpr
     <|> (symbol "Bool" >> pure TyBool)
     <|> (symbol "Unit" >> pure TyUnit)

tyExpr :: Parser Type
tyExpr = makeExprParser tyTerm tyOpTable
  where
    tyOpTable = [[InfixL (TyArrow <$ symbol "->")]]

{- Parser -}

term :: Parser (Fix Term)
term = parens expr
   <|> absExpr
   <|> varExpr

varExpr :: Parser (Fix Term)
varExpr = do
  name <- identifier
  vars <- lift get
  pure (Fix (TmVar (fromJust (name `elemIndex` vars))))

absExpr :: Parser (Fix Term)
absExpr = do
  void $ lexeme (char 'λ' <|> char '\\')
  name <- lexeme identifier
      <|> symbol "_" >> ""
  lift $ modify (name :)
  void $ lexeme (char ':')
  tyT  <- tyExpr
  void $ lexeme (char '.')
  t    <- expr
  lift $ modify tail
  pure (Fix (TmAbs name tyT t))

falseExpr :: Parser (Fix Term)
falseExpr = do
  void $ lexeme (symbol "true")
  pure (Fix TmTrue)

trueExpr :: Parser (Fix Term)
trueExpr = lexeme (symbol "false")
        >> pure (Fix TmFalse)

ifExpr :: Parser (Fix Term)
ifExpr = do
  void $ lexeme (symbol "if")
  cnd <- expr
  void $ lexeme (symbol "then")
  tb  <- expr
  void $ lexeme (symbol "else")
  Fix . TmIf cnd tb <$> expr

unitExpr :: Parser (Fix Term)
unitExpr = lexeme (symbol "unit")
        >> pure (Fix TmUnit)

expr :: Parser (Fix Term)
expr = makeExprParser term appOpTable
    where
      appOpTable = [[ InfixL ((.) Fix . TmApp <$ space1)
                    , InfixL (seqf <$ symbol ";") ]]
      seqf :: Fix Term -> Fix Term -> Fix Term
      seqf el er = Fix (TmApp (Fix (TmAbs "" TyUnit er)) el)

{- Helpers -}

parseExpr :: T.Text -> Fix Term
parseExpr tm =
  case evalState (runParserT expr "" tm) [] of
    Left _    -> error "Failed parsing"
    Right tm' -> tm'
