{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Typed.Boolean where

import           Data.Functor.Classes                  (Show1 (..))
import           Data.Functor.Foldable                 (Fix (..), para)
import qualified Data.HashMap.Strict.InsOrd            as M
import           Data.List                             (elemIndex)
import           Data.Maybe                            (fromJust)
import qualified Data.Text                             as T
import           Text.Show                             (showString)
import Safe

-- Printing
import           Data.Text.Prettyprint.Doc             (Doc, Pretty (..), defaultLayoutOptions, layoutSmart, (<+>),
                                                        (<>))
import qualified Data.Text.Prettyprint.Doc             as D (parens)
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)

-- Parsing
import           Control.Monad                         (void)
import qualified Control.Monad.Trans.Class             as MT (MonadTrans (..))
import qualified Control.Monad.Trans.State             as MT (State (..), evalState, get, modify)
import           Data.Either                           (fromRight)
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer            as L
import           Text.Megaparsec.Expr

{- AST -}

data Type = TyArrow Type Type
          | TyBoolean
          deriving (Eq)

instance Show Type where
  show (TyArrow tyT1 tyT2) = "(" ++ show tyT1 ++ " → " ++ show tyT2 ++ ")"
  show TyBoolean = "Bool"

newtype Binding = VarBinding Type
                deriving (Show, Eq)

data Term a = TmVar Int
            | TmAbs T.Text Type a
            | TmApp a a
            | TmTrue
            | TmFalse
            | TmIf a a a
            deriving (Show, Eq, Functor)

type Context = [(T.Text, Binding)]

addBinding :: Context -> T.Text -> Type -> Context
addBinding ctx name ty = (name, VarBinding ty) : ctx

getBinding :: Context -> Int -> Either T.Text (T.Text, Type)
getBinding ctx index =
  case atMay ctx index of
    Nothing              -> Left "Looked up index does not exist."
    Just (x, VarBinding tyT1) -> Right (x, tyT1)

getType :: Context -> Int -> Either T.Text Type
getType = (.) (fmap snd) . getBinding

getName :: Context -> Int -> Either T.Text T.Text
getName = (.) (fmap fst) . getBinding

pickFreshName :: Context -> T.Text -> Type -> (Context, T.Text)
pickFreshName ctx name ty =
  case lookup name ctx of
    Nothing -> (addBinding ctx name ty, name)
    Just _  -> pickFreshName ctx (name `T.append` "\'") ty

{- Typechecker -}

typeOf :: Context -> Fix Term -> Either T.Text Type
typeOf ctx (Fix (TmVar index)) = getType ctx index
typeOf ctx (Fix (TmAbs name tyT1 t2)) = do
  let ctx' = addBinding ctx name tyT1
  tyT2 <- typeOf ctx' t2
  return (TyArrow tyT1 tyT2)
typeOf ctx (Fix (TmApp t1 t2)) = do
  tyT1 <- typeOf ctx t1
  tyT2 <- typeOf ctx t2
  case tyT1 of
    TyArrow tyT11 tyT12 ->
      if tyT2 == tyT12 then Right tyT12
      else Left "parameter type mismatch"
    _ -> Left "arrow type expected"
typeOf ctx (Fix TmTrue) = Right TyBoolean
typeOf ctx (Fix TmFalse) = Right TyBoolean
typeOf ctx (Fix (TmIf t1 t2 t3)) = do
  tyT1 <- typeOf ctx t1
  if tyT1 == TyBoolean then do
    tyT2 <- typeOf ctx t2
    tyT3 <- typeOf ctx t3
    if tyT2 == tyT3 then Right tyT2
    else Left "arms of conditional have different types"
  else Left "guard of conditional is not a boolean"

{- Pretty printing -}

instance Show1 Term where
  liftShowsPrec _ _ d (TmVar index)     = showString (show index)
  liftShowsPrec showT _ d (TmAbs x tyT1 t2)   =
    showString "(λ" . showText x
                        . showString ":" . showString (show tyT1) . showString ". "
                    . showT (d + 1) t2 . showString ")"
  liftShowsPrec showT _ d (TmApp t1 t2) =
    showString "(" . showT (d + 1) t1 . showString " "
                   . showT (d + 1) t2 . showString ")"

showText :: T.Text -> ShowS
showText = showString . T.unpack

instance Pretty (Fix Term) where
  pretty :: Fix Term -> Doc ann
  pretty term = para ralg term'
    where
      renameVars :: Context -> Fix Term -> (Context, Fix Term)
      renameVars ctx (Fix (TmAbs x tyT2 t2)) =
        let (ctx' , freshName) = pickFreshName ctx x tyT2
            (ctx'', t2') = renameVars ctx' t2
        in  (ctx'', Fix (TmAbs freshName tyT2 t2'))
      renameVars ctx (Fix (TmApp t1 t2)) =
        let (ctx' , t1') = renameVars ctx t1
            (ctx'', t2') = renameVars ctx' t2
        in  (ctx'', Fix (TmApp t1' t2'))
      renameVars ctx t = (ctx, t)
      (context, term') = renameVars [] term

      -- Do not show parenthesis around variables
      vparens :: (Fix Term, Doc ann) -> Doc ann
      vparens (Fix (TmVar _), tm) = tm
      vparens (_, tm)             = D.parens tm

      ralg :: Term (Fix Term, Doc ann) -> Doc ann
      ralg (TmApp (Fix (TmApp _ _), t1) (_ , t2)) = t1 <+> t2
      ralg (TmApp t1 t2)                          = vparens t1 <+> vparens t2
      ralg (TmAbs x tyT2 (Fix TmAbs{}, t2)) =
        "λ" <> pretty x <> ":" <> pretty (show tyT2) <> "." <+> t2
      ralg (TmAbs x tyT2 t2)                      =
        "λ" <> pretty x <> ":" <> pretty (show tyT2) <> "." <+> snd t2
      ralg (TmVar index)                          = pretty (fromRight "" $ getName context index)

render :: Fix Term -> T.Text
render = renderStrict . layoutSmart defaultLayoutOptions . pretty

{- Substitution -}

termShift :: Int       -- ^ Depth of the term (d)
          -> Fix Term  -- ^ The term we are shifting
          -> Fix Term  -- ^ The result of the shift
termShift d = go d 0
  where
    go :: Int -> Int -> Fix Term -> Fix Term
    go d c (Fix (TmVar index))  =
      let index' = if index > c then index + d
                                else index
      in  Fix (TmVar index')
    go d c (Fix (TmAbs name tyT t)) =
      Fix (TmAbs name tyT (go d (c + 1) t))
    go d c (Fix (TmApp t1 t2))  =
      Fix (TmApp (go d c t1) (go d c t2))

termSubst :: Int       -- ^ The variable index we are substituting (j)
          -> Fix Term  -- ^ The expression we subst. for the variable (s)
          -> Fix Term  -- ^ The expression where the subst. takes place (t)
          -> Fix Term  -- ^ The substitution result
termSubst j s = go 0
  where
    go :: Int -> Fix Term -> Fix Term
    go c (Fix (TmVar index)) =
      if index == j + c then termShift c s
                        else Fix (TmVar index)
    go c (Fix (TmAbs name tyT t)) = Fix (TmAbs name tyT (go (c + 1) t))
    go c (Fix (TmApp t1 t2 )) = Fix (TmApp (go c t1) (go c t2))

termSubstTop :: Fix Term -> Fix Term -> Fix Term
termSubstTop s t = termShift (-1) (termSubst 0 (termShift 1 s) t)

{- Lexer -}

type Parser = ParsecT Void T.Text (MT.State VarContext)

type VarContext = [T.Text]

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: T.Text -> Parser T.Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

-- ^ Identifier is a letter followed by a number of primes
identifier :: Parser T.Text
identifier =
  T.pack <$> ((:) <$> letterChar <*> many (char '\''))

tyTerm :: Parser Type
tyTerm = parens tyExpr
     <|> (symbol "Bool" >> return TyBoolean)

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
  vars <- MT.lift MT.get
  return (Fix (TmVar (fromJust (name `elemIndex` vars))))

absExpr :: Parser (Fix Term)
absExpr = do
  lam  <- lexeme (char 'λ' <|> char '\\')
  name <- lexeme identifier
  MT.lift $ MT.modify (name :)
  lexeme (char ':')
  tyT <- tyExpr
  lexeme (char '.')
  term <- expr
  MT.lift $ MT.modify tail
  pure (Fix (TmAbs name tyT term))

expr :: Parser (Fix Term)
expr = makeExprParser term appOpTable
  where
    appOpTable = [[InfixL ((.) Fix . TmApp <$ space1)]]

{- Helper functions -}

parseExpr :: T.Text -> Fix Term
parseExpr t = case parseResult of
  Left _ -> error "Failed parsing"
  Right t -> t
  where
    parseResult = MT.evalState (runParserT expr "" t) []

