{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE OverloadedStrings #-}

module Typed.Simple.Types where

import           Control.Comonad                  (extend)
import           Control.Comonad.Cofree           (Cofree (..))
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (ExceptT (..), runExceptT, throwE)
import           Control.Monad.Trans.State.Strict (evalState, get, gets, modify, State)
import           Data.Functor.Foldable            (Fix (..))
import qualified Data.HashMap.Strict.InsOrd       as Map (InsOrdHashMap, empty, insert, lookup)
import           Data.Maybe                       (maybe)
import           Data.Text                        as T (Text)

import           Typed.Simple.Syntax

data TypeCheckContext = TypeCheckContext
  { context :: Context
  , memos   :: Map.InsOrdHashMap (Cofree Term ()) Type
  }

type TypeCheck a = ExceptT T.Text (State TypeCheckContext) a

updateContext :: (Context -> Context) -> TypeCheck ()
updateContext f = lift $ modify (\(TypeCheckContext c m) -> TypeCheckContext (f c) m)

emptyContext :: TypeCheckContext
emptyContext = TypeCheckContext [] Map.empty

memoized :: (Cofree Term () -> TypeCheck Type) -> Cofree Term () -> TypeCheck Type
memoized f t = Map.lookup t <$> mTable >>= maybe mAdd return
  where
    mTable :: TypeCheck (Map.InsOrdHashMap (Cofree Term ()) Type)
    mTable = lift $ gets memos
    mAdd :: TypeCheck Type
    mAdd = do
      ty <- f t
      lift $ modify (\(TypeCheckContext c m) ->
                       TypeCheckContext c (Map.insert t ty m))
      return ty

makeAnnotation :: Functor f => Fix f -> Cofree f ()
makeAnnotation (Fix f) = () :< fmap makeAnnotation f

generateTypes :: Cofree Term () -> TypeCheck Type
generateTypes (() :< TmTrue) = pure TyBool
generateTypes (() :< TmFalse) = pure TyBool
generateTypes (() :< TmAbs name tyT t) = do
  updateContext ((name, tyT) :)
  tT <- memoized generateTypes t
  updateContext tail
  pure (TyArrow tyT tT)
generateTypes (() :< TmApp t1 t2) = do
  TyArrow tyT11 tyT12 <- memoized generateTypes t1
  tyT2 <- memoized generateTypes t2
  if tyT2 /= tyT11 then throwE "Application to expression of wrong type."
                   else pure tyT12
generateTypes (() :< TmVar index) = do
  TypeCheckContext ctx _ <- lift get
  case getType ctx index of
    Left err -> throwE err
    Right ty -> pure ty
generateTypes (() :< TmIf cnd tb eb) = do
  cndT <- memoized generateTypes cnd
  tbT <- memoized generateTypes tb
  ebT <- memoized generateTypes eb
  if cndT /= TyBool
  then throwE "The condition in an `if` statement should have type `Bool`."
  else
    if tbT /= ebT
    then throwE "The branched of an `if` statement should have the same type."
    else pure tbT

annotate :: Cofree Term () -> Either T.Text (Cofree Term Type)
annotate t = evalState (runExceptT (sequence $ extend (memoized generateTypes) t)) emptyContext
