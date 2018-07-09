module Lib
    ( someFunc
    ) where

someFunc :: IO ()
someFunc = putStrLn "someFunc"

newtype Cont r a = Cont { runCont :: (a -> r) -> r }
