{-# LANGUAGE GADTs, TypeFamilies, UndecidableInstances, AllowAmbiguousTypes #-}

{-# OPTIONS -Wno-tabs #-}

module Main where

import Debug.Trace

import ES

data FTrue = FTrue deriving (Eq, Ord, Show)
instance Fact FTrue where
	getIDs _ = []
	changeIDs f [] = f
data FFalse = FFalse deriving (Eq, Ord, Show)
instance Fact FFalse where
	getIDs _ = []
	changeIDs f [] = f
data Negate = Negate ID deriving (Eq, Ord, Show)
instance Fact Negate where
	getIDs (Negate i) = [i]
	changeIDs _ [i] = Negate i


namedRule :: Monad m => String -> Rule m -> (String, Rule m)
namedRule s r = (s, r)

negateFalse :: NamedRule IO
negateFalse = namedRule "negate false" $ \s -> do
	start <- changes s 1
	onIDs s $ \(n, Negate i) -> onID i $ \(_, FFalse) -> do { j <- add FTrue; n === j}

test = do
	f <- add FFalse
	n <- add (Negate f)
	getESEnv >>= \x -> liftES (print x)
	runRules [negateFalse]
	getESEnv >>= \x -> liftES (print x)

t = runESM test

main = do
	t
	return ()
