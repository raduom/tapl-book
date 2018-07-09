{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE OverloadedStrings #-}

module Typed.Simple.Syntax where

import           Control.Comonad.Cofree                (Cofree (..))
import           Data.Functor.Classes                  (Eq1 (..), Show1 (..))
import           Data.Functor.Foldable                 (Fix (..), para)
import           Data.Hashable                         (Hashable (..))
import qualified Data.Text                             as T
import           GHC.Generics                          (Generic)

import           Data.Either                           (fromRight)
import           Data.Text.Prettyprint.Doc             (Doc, Pretty (..), defaultLayoutOptions, layoutSmart, parens,
                                                        (<+>), (<>))
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import           Safe                                  (atMay)

data Term a = TmVar Int
            | TmAbs T.Text Type a
            | TmApp a a
            | TmTrue
            | TmFalse
            | TmIf a a a
            deriving (Show, Eq, Functor, Foldable, Traversable, Generic)

data Type = TyArrow Type Type
          | TyBool
          deriving (Eq, Generic, Hashable)

type Binding = Type

type Context = [(T.Text, Binding)]

instance Show Type where
  show (TyArrow tyT1 tyT2) = "(" ++ show tyT1 ++ " → " ++ show tyT2 ++ ")"
  show TyBool              = "Bool"

instance Show1 Term where
  liftShowsPrec _ _ _ (TmVar index)     = showString (show index)
  liftShowsPrec showT _ d (TmAbs x tyT1 t2)   =
    showString "(λ" . showText x
                        . showString ":" . showString (show tyT1) . showString ". "
                    . showT (d + 1) t2 . showString ")"
  liftShowsPrec showT _ d (TmApp t1 t2) =
    showString "(" . showT (d + 1) t1 . showString " "
                   . showT (d + 1) t2 . showString ")"
  liftShowsPrec showT _ d (TmIf c b1 b2) =
    showString "if " . showT (d + 1) c
    . showString " then " . showT (d + 1) b1
    . showString " else " . showT (d + 1) b2
  liftShowsPrec _ _ _ TmTrue = showString "true"
  liftShowsPrec _ _ _ TmFalse = showString "false"

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

removeBinding :: Context -> T.Text -> Context
removeBinding ctx l = filter ((l /=) . fst) ctx

addBinding :: Context -> T.Text -> Type -> Context
addBinding ctx name ty = (name, ty) : ctx

getBinding :: Context -> Int -> Either T.Text (T.Text, Type)
getBinding ctx index =
  case atMay ctx index of
    Nothing -> Left "Looked up index does not exist."
    Just b  -> Right b

getType :: Context -> Int -> Either T.Text Type
getType = (.) (fmap snd) . getBinding

getName :: Context -> Int -> Either T.Text T.Text
getName = (.) (fmap fst) . getBinding

pickFreshName :: Context -> T.Text -> Type -> (Context, T.Text)
pickFreshName ctx name ty =
  case lookup name ctx of
    Nothing -> (addBinding ctx name ty, name)
    Just _  -> pickFreshName ctx (name `T.append` "\''") ty

{- Substitution -}

termShift :: Int
          -> Fix Term
          -> Fix Term
termShift d = go d 0
  where
    go :: Int -> Int -> Fix Term -> Fix Term
    go d' c (Fix (TmVar index)) =
      let index' = if index > c then index + d'
                                else index
      in Fix (TmVar index')
    go d' c (Fix (TmAbs name tyT t)) =
      Fix (TmAbs name tyT (go d' (c + 1) t))
    go d' c (Fix (TmApp t1 t2)) =
      Fix (TmApp (go d' c t1) (go d' c t2))
    go d' c (Fix (TmIf cnd tb eb)) =
      Fix (TmIf (go d' c cnd) (go d' c tb) (go d' c eb))
    go _ _ tmTrueOrFalse = tmTrueOrFalse

termSubst :: Int
          -> Fix Term
          -> Fix Term
          -> Fix Term
termSubst j s = go 0
  where
    go :: Int -> Fix Term -> Fix Term
    go c (Fix (TmVar index)) =
      if index == j + c then termShift c s
                        else Fix (TmVar index)
    go c (Fix (TmAbs name tyT t)) =
      Fix (TmAbs name tyT (go (c + 1) (termShift 1 t)))
    go c (Fix (TmApp t1 t2)) = Fix (TmApp (go c t1) (go c t2))
    go c (Fix (TmIf cnd tb eb)) = Fix (TmIf (go c cnd) (go c tb) (go c eb))
    go _ tmTrueOrFalse = tmTrueOrFalse

instance Pretty (Fix Term) where
  pretty :: Fix Term -> Doc ann
  pretty tm = para ralg namedTerm
    where
      nameVars :: Context -> Fix Term -> (Context, Fix Term)
      nameVars ctx (Fix (TmAbs x tyT t)) =
        let (ctx' , freshName) = pickFreshName ctx x tyT
            (ctx'', t') = nameVars ctx' t
        in  (ctx'', Fix (TmAbs freshName tyT t'))
      nameVars ctx (Fix (TmApp t1 t2)) =
        let (ctx' , t1') = nameVars ctx  t1
            (ctx'', t2') = nameVars ctx' t2
        in  (ctx'', Fix (TmApp t1' t2'))
      nameVars ctx (Fix (TmIf cnd tb eb)) =
        let (ctx'  , cnd') = nameVars ctx   cnd
            (ctx'' , tb' ) = nameVars ctx'  tb
            (ctx''', eb' ) = nameVars ctx'' eb
        in  (ctx''', Fix (TmIf cnd' tb' eb'))
      nameVars ctx tm' = (ctx, tm')
      (context, namedTerm)  = nameVars [] tm

      vp :: (Fix Term, Doc ann) -> Doc ann
      vp (Fix (TmVar _), tm') = tm'
      vp (_            , tm') = parens tm'

      ralg :: Term (Fix Term, Doc ann) -> Doc ann
      ralg TmTrue = "true"
      ralg TmFalse = "false"
      ralg (TmApp (Fix (TmApp _ _), t1) (_, t2)) = t1 <+> t2
      ralg (TmApp t1 t2)                         = vp t1 <+> vp t2
      ralg (TmAbs x tyT (Fix TmAbs{}, t))        =
        "λ" <> pretty x <> ":" <> pretty (show tyT) <> "." <+> t
      ralg (TmAbs x tyT t)                       =
        "λ" <> pretty x <> ":" <> pretty (show tyT) <> "." <+> snd t
      ralg (TmVar index)                         =
        pretty (fromRight "" $ getName context index)
      ralg (TmIf cnd tb eb) =
        "if" <+> vp cnd <> "then" <+> vp tb <+> "else" <+> vp eb

render :: Fix Term -> T.Text
render = renderStrict . layoutSmart defaultLayoutOptions . pretty
