{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE OverloadedStrings #-}
module Untyped.Lambda where

import           Data.Functor.Classes                  (Show1 (..))
import           Data.Functor.Foldable                 (Fix (..), para)
import qualified Data.HashMap.Strict.InsOrd            as M
import           Data.List                             (elemIndex)
import           Data.Maybe                            (fromJust)
import qualified Data.Text                             as T
import           Text.Show                             (showString)

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

import Debug.Trace

{- AST -}
data Term a = TmVar Int
            | TmAbs T.Text a
            | TmApp a a
            deriving (Eq, Show, Functor)

{- Context definition and associated functions -}
type Context = M.InsOrdHashMap T.Text Binding

data Binding = NameBind
               deriving (Show, Eq)

ctxLength :: Context -> Int
ctxLength = M.size

indexToName :: Context -> Int -> T.Text
indexToName ctx index = reverse (M.keys ctx) !! index

pickFreshName :: Context -> T.Text -> (Context, T.Text)
pickFreshName ctx name =
  if M.member name ctx then pickFreshName ctx (name `T.append` "'")
                       else (M.insert name NameBind ctx, name)

-- This is already defined as a catamorphism, but there are
-- no parenethesis optimisations. Will use this for testing
instance Show1 Term where
  liftShowsPrec _ _ d (TmVar index)     = showString (show index)
  liftShowsPrec showT _ d (TmAbs l t)   =
    showString "(λ" . showText l . showString ". "
                    . showT (d + 1) t . showString ")"
  liftShowsPrec showT _ d (TmApp t1 t2) =
    showString "(" . showT (d + 1) t1 . showString " "
                   . showT (d + 1) t2 . showString ")"

showText :: T.Text -> ShowS
showText = showString . T.unpack

-- Lets apply the optimizations proposed in the book for
-- omitting parentheses in applications and abstractions
-- by using a paramorphism to check the structure of the term
instance Pretty (Fix Term) where
  pretty :: Fix Term -> Doc ann
  pretty term = para ralg term'
    where
      renameVars :: Context -> Fix Term -> (Context, Fix Term)
      renameVars ctx (Fix (TmAbs name t)) =
        let (ctx' , freshName) = pickFreshName ctx name
            (ctx'', t') = renameVars ctx' t
        in  (ctx'', Fix (TmAbs freshName t'))
      renameVars ctx (Fix (TmApp t1 t2)) =
        let (ctx' , t1') = renameVars ctx t1
            (ctx'', t2') = renameVars ctx' t2
        in  (ctx'', Fix (TmApp t1' t2'))
      renameVars ctx t = (ctx, t)
      (context, term') = renameVars M.empty term

      -- Do not show parenthesis around variables
      vparens :: (Fix Term, Doc ann) -> Doc ann
      vparens (Fix (TmVar _), tm) = tm
      vparens (_, tm)             = D.parens tm

      ralg :: Term (Fix Term, Doc ann) -> Doc ann
      ralg (TmApp (Fix (TmApp _ _), t1) (_ , t2)) = t1 <+> t2
      ralg (TmApp t1 t2)                          = vparens t1 <+> vparens t2
      ralg (TmAbs name (Fix (TmAbs _ _), t))      = "λ" <> pretty name <> "." <+> t
      ralg (TmAbs name t)                         = "λ" <> pretty name <> "." <+> vparens t
      ralg (TmVar index)                          = pretty (indexToName context index)

render :: Fix Term -> T.Text
render = renderStrict . layoutSmart defaultLayoutOptions . pretty

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
    go d c (Fix (TmAbs name t)) =
      Fix (TmAbs name (go d (c + 1) t))
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
    go c (Fix (TmAbs name t)) = Fix (TmAbs name (go (c + 1) t))
    go c (Fix (TmApp t1 t2 )) = Fix (TmApp (go c t1) (go c t2))

termSubstTop :: Fix Term -> Fix Term -> Fix Term
termSubstTop s t = termShift (-1) (termSubst 0 (termShift 1 s) t)

isValue :: Fix Term -> Bool
isValue (Fix (TmAbs _ _)) = True
isValue _                 = False

{- Lexer -}
type Parser = ParsecT Void T.Text (MT.State VarContext)

type VarContext = [T.Text]

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

-- ^ Identifier is a letter followed by a number of primes
identifier :: Parser T.Text
identifier =
  T.pack <$> ((:) <$> letterChar <*> many (char '\''))

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
  lexeme (char '.')
  term <- expr
  MT.lift $ MT.modify tail
  pure (Fix (TmAbs name term))

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
