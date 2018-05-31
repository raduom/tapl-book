{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE OverloadedStrings #-}
module Typed.Boolean where

import           Control.Comonad                       (Comonad (..))
import           Control.Comonad.Cofree                (Cofree (..))
import           Data.Functor.Classes                  (Eq1 (..), Show1 (..))
import           Data.Functor.Foldable                 (Fix (..), para)
import           Data.Hashable                         (Hashable (..))
import           Data.Hashable.Lifted                  (Hashable1 (..))
import qualified Data.HashMap.Strict.InsOrd            as Map
import           Data.List                             (elemIndex)
import           Data.Maybe                            (fromJust, maybe)
import qualified Data.Text                             as T
import           GHC.Generics
import           Safe
import           Text.Show                             (showString)

-- Printing
import           Data.Text.Prettyprint.Doc             (Doc, Pretty (..), defaultLayoutOptions, layoutSmart, (<+>),
                                                        (<>))
import qualified Data.Text.Prettyprint.Doc             as D (parens)
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)

-- Parsing
import           Control.Monad                         (void)
import           Control.Monad.Trans.Class             (MonadTrans (..), lift)
import           Control.Monad.Trans.Except            (ExceptT (..), runExceptT, throwE)
import           Control.Monad.Trans.State.Strict      (evalState, get, gets, modify)
import qualified Control.Monad.Trans.State.Strict      as S (State (..))
import           Data.Either                           (fromRight)
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer            as L
import           Text.Megaparsec.Expr

import           Debug.Trace

{- AST -}

data Type = TyArrow Type Type
          | TyBoolean
          deriving (Eq, Generic, Hashable)

instance Show Type where
  show (TyArrow tyT1 tyT2) = "(" ++ show tyT1 ++ " → " ++ show tyT2 ++ ")"
  show TyBoolean           = "Bool"

type Binding = Type

data Term a = TmVar Int
            | TmAbs T.Text Type a
            | TmApp a a
            | TmTrue
            | TmFalse
            | TmIf a a a
            deriving (Show, Eq, Functor, Foldable, Traversable, Generic)

type Context = [(T.Text, Binding)]

removeBinding :: Context -> T.Text -> Context
removeBinding ctx l = filter ((l /=) . fst) ctx

addBinding :: Context -> T.Text -> Type -> Context
addBinding ctx name ty = (name, ty) : ctx

getBinding :: Context -> Int -> Either T.Text (T.Text, Type)
getBinding ctx index =
  case atMay ctx index of
    Nothing                   -> Left "Looked up index does not exist."
    Just (x, tyT1) -> Right (x, tyT1)

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

instance Eq1 Term where
  liftEq _ TmFalse TmFalse                     = True
  liftEq _ TmTrue TmTrue                       = True
  liftEq eq (TmIf t1 t2 t3) (TmIf t1' t2' t3') =
    t1 `eq` t1' && t2 `eq` t2' && t3 `eq` t3'
  liftEq eq (TmAbs v ty t) (TmAbs v' ty' t')   =
    v == v' && ty == ty' && t `eq` t'
  liftEq eq (TmApp t1 t2) (TmApp t1' t2')      =
    t1 `eq` t1' && t2 `eq` t2'
  liftEq _ (TmVar idx) (TmVar idx')            = idx == idx'
  liftEq _ _ _ = False

instance Hashable (Cofree Term ()) where
  hashWithSalt s (() :< TmTrue)        = s `hashWithSalt` (0 :: Int)
  hashWithSalt s (() :< TmFalse)       = s `hashWithSalt` (1 :: Int)
  hashWithSalt s (() :< TmIf t1 t2 t3) = s `hashWithSalt`
                                         (2 :: Int) `hashWithSalt`
                                         t1 `hashWithSalt`
                                         t2 `hashWithSalt` t3
  hashWithSalt s (() :< TmAbs v ty t)  = s `hashWithSalt`
                                         (3 :: Int) `hashWithSalt`
                                         v `hashWithSalt`
                                         ty `hashWithSalt` t
  hashWithSalt s (() :< TmApp t1 t2)   = s `hashWithSalt`
                                         (4 :: Int) `hashWithSalt`
                                         t1 `hashWithSalt` t2
  hashWithSalt s (() :< TmVar index)   = s `hashWithSalt`
                                         (5 :: Int) `hashWithSalt` index

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

type Parser = ParsecT Void T.Text (S.State VarContext)

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
  vars <- lift get
  return (Fix (TmVar (fromJust (name `elemIndex` vars))))

absExpr :: Parser (Fix Term)
absExpr = do
  lam  <- lexeme (char 'λ' <|> char '\\')
  name <- lexeme identifier
  lift $ modify (name :)
  lexeme (char ':')
  tyT <- tyExpr
  lexeme (char '.')
  term <- expr
  lift $ modify tail
  pure (Fix (TmAbs name tyT term))

expr :: Parser (Fix Term)
expr = makeExprParser term appOpTable
  where
    appOpTable = [[InfixL ((.) Fix . TmApp <$ space1)]]

{- Helper functions -}

parseExpr :: T.Text -> Fix Term
parseExpr t = case parseResult of
  Left _  -> error "Failed parsing"
  Right t -> t
  where
    parseResult = evalState (runParserT expr "" t) []

{- Type annotated AST -}

data TypeCheckContext = TypeCheckContext
     { context :: Context
     , memos   :: Map.InsOrdHashMap (Cofree Term ()) Type
     }

type TypeCheck a = ExceptT T.Text (S.State TypeCheckContext) a

updateContext :: (Context -> Context) -> TypeCheck ()
updateContext f = lift $ modify (\(TypeCheckContext c m) -> TypeCheckContext (f c) m)

emptyContext :: TypeCheckContext
emptyContext = TypeCheckContext [] Map.empty

memoized :: (Cofree Term () -> TypeCheck Type) -> Cofree Term () -> TypeCheck Type
memoized f t = Map.lookup t <$> mTable >>= maybe mAdd return
  where
    mTable :: TypeCheck (Map.InsOrdHashMap (Cofree Term ()) Type)
    mTable =  lift $ gets memos
    mAdd :: TypeCheck Type
    mAdd = do
      ty <- f t
      lift $ modify (\(TypeCheckContext c m) ->
                       TypeCheckContext c (Map.insert t ty m))
      return ty

makeAnnotation :: Functor f => Fix f -> Cofree f ()
makeAnnotation (Fix f) = () :< fmap makeAnnotation f

generateTypes :: Cofree Term () -> TypeCheck Type
generateTypes (() :< TmTrue)  = return TyBoolean
generateTypes (() :< TmFalse) = return TyBoolean
generateTypes (() :< TmAbs name ty t) = do
  updateContext ((name, ty) :)
  tT <- memoized generateTypes t
  updateContext tail
  return (TyArrow ty tT)
generateTypes (() :< TmApp t1 t2) = do
  (TyArrow tyT11 tyT12) <- generateTypes t1
  tyT2 <- memoized generateTypes t2
  if tyT2 /= tyT11 then throwE "Application to expression with wrong type."
                   else return tyT12
generateTypes t@(() :< TmVar index) = do
  TypeCheckContext ctx _ <- lift get
  case getType ctx index  of
    Left err -> throwE err
    Right ty -> return ty
generateTypes (() :< TmIf t1 t2 t3) = do
  t1T <- memoized generateTypes t1
  t2T <- memoized generateTypes t2
  t3T <- memoized generateTypes t3
  if t1T /= TyBoolean
  then throwE "If's condition should be Bool."
  else
    if t2T /= t3T
    then throwE "If's branches must have the same type."
    else return t2T

annotate :: Cofree Term () -> Either T.Text (Cofree Term Type)
annotate t = evalState (runExceptT (sequence $ extend (memoized generateTypes) t)) emptyContext

{- Debugging -}

-- dbgTable :: TypeCheck ()
-- dbgTable = do
--   tbl <- lift $ gets memos
--   trace ("Table: " ++ show tbl ++ "\n") $ return ()

-- dbgMsg :: Show a => a -> TypeCheck ()
-- dbgMsg msg = trace ("debug: " ++ show msg) $ return ()
