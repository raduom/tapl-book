{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE OverloadedStrings #-}
module Untyped.Lambda where

import           Data.Functor.Classes                  (Show1(..))
import           Data.Functor.Foldable                 (Fix(..), para)
import qualified Data.HashMap.Strict.InsOrd            as M
import           Data.Maybe                            (fromJust)
import qualified Data.Text                             as T
import           Text.Show                             (showString)

-- Printing
import           Data.Text.Prettyprint.Doc             (Doc, Pretty (..), defaultLayoutOptions, layoutSmart, (<+>),
                                                        (<>),parens)
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)

{- AST -}
data Term a = TmVar Int
            | TmAbs T.Text a
            | TmApp a a
            deriving (Eq, Show, Functor)

{- Context definition and associated functions -}
type Context = M.InsOrdHashMap T.Text Binding

data Binding = NameBind

ctxLength :: Context -> Int
ctxLength = M.size

indexToName :: Context -> Int -> T.Text
indexToName ctx index = M.keys ctx !! index

pickFreshName :: Context -> T.Text -> (Context, T.Text)
pickFreshName ctx name =
  if M.member name ctx then pickFreshName ctx (name `T.append` "'")
                       else (M.insert name NameBind ctx, name)

-- This is already defined as a catamorphism, but there are
-- no parenethesis optimisations. Will use this for testing
instance Show1 Term where
  liftShowsPrec _ _ d (TmVar index)     = showString (show index)
  liftShowsPrec showT _ d (TmAbs l t)   =
    showString "(λ" . shows l . showString ". "
                    . showT (d + 1) t . showString ")"
  liftShowsPrec showT _ d (TmApp t1 t2) =
    showString "(" . showT (d + 1) t1 . showString " "
                   . showT (d + 1) t2 . showString ")"

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
      renameVars ctx t = (ctx, t)
      (context, term') = renameVars M.empty term

      -- Do not show parenthesis around variables
      vparens :: (Fix Term, Doc ann) -> Doc ann
      vparens (Fix (TmVar _), tm) = tm
      vparens (_, tm) = parens tm

      ralg :: Term (Fix Term, Doc ann) -> Doc ann
      ralg (TmApp (Fix (TmApp _ _), t1) (_ , t2)) = t1 <+> t2
      ralg (TmApp t1 t2) = vparens t1 <+> vparens t2
      ralg (TmAbs name (Fix (TmAbs _ _), t)) = "λ" <> pretty name <> "." <+> t
      ralg (TmAbs name t) = "λ" <> pretty name <> "." <+> vparens t
      ralg (TmVar index) = pretty (indexToName context index)

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
isValue _ = False

{- Parser -}


