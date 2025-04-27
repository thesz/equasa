{-# LANGUAGE GADTs, TypeFamilies, UndecidableInstances, AllowAmbiguousTypes #-}

{-# OPTIONS -Wno-tabs #-}

module Main where

import Control.Monad

import Control.Monad.State

import Data.Bits

import qualified Data.Map as Map
import qualified Data.Set as Set

import System.IO

import ES

data FTrue = FTrue deriving (Eq, Ord, Show)
instance Fact FTrue where
	getIDs _ = []
	changeIDs f [] = f
data FFalse = FFalse deriving (Eq, Ord, Show)
instance Fact FFalse where
	getIDs _ = []
	changeIDs f [] = f
data Negate = Negate !ID deriving (Eq, Ord, Show)
instance Fact Negate where
	getIDs (Negate i) = [i]
	changeIDs _ [i] = Negate i

data Input = Input !Int deriving (Eq, Ord, Show)
instance Fact Input where
	getIDs (Input _) = []
	changeIDs x [] = x

data M = M !ID !ID !ID deriving (Eq, Ord, Show)
instance Fact M where
	getIDs (M a b c) = [a,b,c]
	changeIDs _ [a,b,c] = M a b c

negateFalseQ :: MQ ((ID,Negate),(ID, FFalse)) (ID, FTrue)
negateFalseQ = ("negate false", m, act)
	where
		(root:f:t:_) = genMatchVars
		m = ((root, Negate f), (f, FFalse))
		act ((root, Negate f), (_, FFalse)) = Just ((t, FTrue), (root, t))

negateTrueQ :: MQ ((ID,Negate),(ID, FTrue)) (ID, FFalse)
negateTrueQ = ("negate true", m, act)
	where
		(root:f:t:_) = genMatchVars
		m = ((root, Negate f), (f, FTrue))
		act ((root, Negate f), (_, FTrue)) = Just ((t, FFalse), (root, t))

doubleNegateQ :: MQ ((ID,Negate),(ID, Negate)) ()
doubleNegateQ = ("double negate", m, act)
	where
		(root:a:b:_) = genMatchVars
		m = ((root, Negate a), (a, Negate b))
		act ((root, Negate a), (_, Negate b)) = Just ((), (root, b))


commuteM1Q :: MQ (ID, M) (ID, M)
commuteM1Q = ("commute abc -> bac", q, act)
	where
		root : a : b : c : d : _ = genMatchVars
		q = (root, M a b c)
		act (root, M a b c) = Just ((d, M b a c), (root, d))
commuteM2Q :: MQ (ID, M) (ID, M)
commuteM2Q = ("commute abc -> cba", q, act)
	where
		root : a : b : c : d : _ = genMatchVars
		q = (root, M a b c)
		act (root, M a b c) = Just ((d, M c a b), (root, d))

negateMQ :: MQ ((ID, Negate), (ID, M)) ((ID, Negate), (ID, Negate), (ID, Negate), (ID, M))
negateMQ = ("negate m", q, act)
	where
		(root : m' : m : a : b : c : a' : b' : c' : _) = genMatchVars
		q = ((root, Negate m'), (m', M a b c))
		act ((root, Negate m'), (_, M a b c)) =
			Just (((a', Negate a), (b', Negate b), (c', Negate c), (m, M a' b' c')), (root, m))

majorityQ :: MQ (ID,M) ()
majorityQ = ("majority", q, act)
	where
		(root : a : b : _) = genMatchVars
		q = ((root, M a a b))
		act ((root, M a _ b)) =
			Just ((), (root, a))

majorityNegQ :: MQ ((ID,M),(ID, Negate)) ()
majorityNegQ = ("majority inv", q, act)
	where
		(root : a : b : c : _) = genMatchVars
		q = ((root, M a b c), (b, Negate a))
		act ((root, M a _ c), (_, Negate _)) =
			Just ((), (root, c))


majorityTrueFalseQ :: MQ ((ID,M),(ID, FTrue), (ID, FFalse)) ()
majorityTrueFalseQ = ("majority true false", q, act)
	where
		(root : m' : a : b : c : _) = genMatchVars
		q = ((root, M a b c), (a, FTrue), (b, FFalse))
		act ((root, M _ _ c), (_, FTrue), (_, FFalse)) =
			Just ((), (root, c))


--rule assoc1_M [M a b [M c b e]] [M e b [M a b e]]
assocMQ :: MQ ((ID, M), (ID, M)) ((ID, M), (ID, M))
assocMQ = ("assoc", q, act)
	where
		(root : u : x : y : z : a : b : c : _) = genMatchVars
		q = ((root, M x u a), (a, M y u z))
		act ((root, M x u _), (_, M y _ z)) = Just (((b, M y u x), (c, M z u b)), (root, c))

distrMQ :: MQ ((ID, M), (ID, M)) ((ID, M), (ID, M), (ID, M))
distrMQ = ("distr", q, act)
	where
		(root : a : b : c : u : v : w : x : y : z : _) = genMatchVars
		q = ((root, M x y w), (w, M u v z))
		act ((root, M x y w), (_, M u v z)) = Just (((a, M x y u), (b, M x y v), (c, M a b z)), (root, c))
distr'MQ :: MQ ((ID, M), (ID, M), (ID, M)) ((ID, M), (ID, M))
distr'MQ = ("distr back", q, act)
	where
		(root : a : b : c : u : v : w : x : y : z : _) = genMatchVars
		q = ((root, M a b z), (a, M x y u), (b, M x y v))
		act ((root, M a b z), (_, M _ _ u), (_, M x y v)) = Just (((w, M u v z), (c, M x y w)), (root, c))

compAssocMQ :: MQ ((ID, M), (ID, M), (ID, Negate)) ((ID, M), (ID, M))
compAssocMQ = ("comp assoc M", q, act)
	where
		(root : a : b : c : t : u : v : w : x : y : z : _) = genMatchVars
		q = ((root, M x u v), (v, M y w z), (w, Negate u))
		act ((root, M x u v), (_, M y w z), (_, Negate _)) = Just (((a, M y x z), (c, M x u a)), (root, c))


land, lor :: ID -> ID -> ESM IO ID
land a b = add FFalse >>= add . M a b

lor a b = add FTrue >>= add . M a b
lnot = add . Negate
lxor x y = do
	x' <- lnot x
	y' <- lnot y
	a <- land x y'
	b <- land x' y
	lor a b

linp :: Monad m => Int -> ESM m ID
linp = add . Input

-- |This creates a truth table (OR of ANDS) of a M operator and finally finds
-- that ``r`` is equal to ``M x y z``.
test1 = do
	x <- add $ Input 0
	y <- add $ Input 1
	z <- add $ Input 2
	tgt <- add $ M x y z
	f <- add FFalse
	t <- add FTrue
	add $ Negate f
	add $ Negate t
	r <- if True
		then do
			let	sel False _ = return []
				sel True invs = do
					abc <- forM (zip [x,y,z] invs) $ \(i,inv) -> do
						if inv then add (Negate i) else return i
					let	[a,b,c] = abc
					z <- land a b
					z <- land z c
					return [z]
			oss <- forM [0..7::Int] $ \n -> sel (popCount n > 1) $ take 3 $ map even $ iterate (`div`2) n
			let	os = concat oss
				joinOr (a:b:abs) = do
					x <- lor a b
					xs <- joinOr abs
					return $ x:xs
				joinOr xs = return xs
				join [z] = return z
				join xs = do
					xs <- joinOr xs
					join xs
			join os
		else add $ M x y z
	traceM $ "r " ++ show r ++ ", tgt " ++ show tgt
	--getESEnv >>= \x -> liftES (print x)
	getESEnv >>= \x -> liftES (mapM_ print $ Map.toList $ eseIDFacts x)
	let	appMatches = do
			ese <- get
			let	oldChanges = eseNewChanged ese
			modify $ \ese -> ese { eseChanged = oldChanges, eseNewChanged = Set.empty }
			let match' r@(name, _, _) = do
				liftES $ do
					putStrLn $ "matching " ++ show name
				match r
			liftES $ do
				putStrLn $ replicate 80 '-'
				putStrLn "-- start"
			match' negateFalseQ
			match' negateTrueQ
			match' assocMQ
			match' distrMQ
			match' commuteM1Q
			match' commuteM2Q
			match' majorityQ
			match' majorityNegQ
			match' majorityTrueFalseQ
			match' negateMQ
			--match' compAssocMQ
			ese <- get
			let	newChanges = eseNewChanged ese
			modify $ \ese -> ese { eseChanged = newChanges }
			let	rClass = Map.findWithDefault undefined r $ eseBelongsTo ese
				tgtClass = Map.findWithDefault undefined tgt $ eseBelongsTo ese
			when (rClass == tgtClass) $ traceM "found answer!"
			traceM $ "set to " ++ show (Set.size newChanges) ++ " new classes"
	forM_ [1..200] $ const appMatches
	--getESEnv >>= \x -> liftES (print x)
	getESEnv >>= \x -> liftES (mapM_ print $ Map.toList $ eseIDFacts x)
	--getESEnv >>= \x -> liftES (mapM_ print $ Map.toList $ eseBelongsTo x)
	getESEnv >>= \x -> liftES (mapM_ print $ Map.toList $ eseClasses x)

-- |From the paper, this is deemed impossible without application of complex derived
--  rules.
test2 = do
	x <- add $ Input 0
	let	tgt = x
	y <- add $ Input 1
	z <- add $ Input 2
	r <- add $ M x y z
	w <- add $ Input 3
	z' <- add $ Negate z
	xyz <- add $ M x y z
	xz'w <- add $ M x z' w
	r <- add $ M x xz'w xyz
	f <- add FFalse
	add $ Negate f
	traceM $ "r " ++ show r ++ ", tgt " ++ show tgt
	--getESEnv >>= \x -> liftES (print x)
	getESEnv >>= \x -> liftES (mapM_ print $ Map.toList $ eseIDFacts x)
	let	appMatches = do
			ese <- get
			let	oldChanges = eseNewChanged ese
			modify $ \ese -> ese { eseChanged = oldChanges, eseNewChanged = Set.empty }
			let match' r@(name, _, _) = do
				liftES $ do
					putStrLn $ "matching " ++ show name
				match r
			liftES $ do
				putStrLn $ replicate 80 '-'
				putStrLn "-- start"
			match' negateFalseQ
			match' negateTrueQ
			match' assocMQ
			match' distrMQ
			--match' distr'MQ
			match' commuteM1Q
			match' commuteM2Q
			match' majorityQ
			match' majorityNegQ
			match' majorityTrueFalseQ
			match' negateMQ
			--match' compAssocMQ
			ese <- get
			let	rClass = Map.findWithDefault undefined r $ eseBelongsTo ese
				tgtClass = Map.findWithDefault undefined tgt $ eseBelongsTo ese
			when (rClass == tgtClass) $ traceM "found answer!"
			let	newChanges = eseChanged ese
			traceM $ "set to " ++ show (Set.size newChanges) ++ " new classes"
	forM_ [1..200] $ const appMatches
	--getESEnv >>= \x -> liftES (print x)
	getESEnv >>= \x -> liftES (mapM_ print $ Map.toList $ eseIDFacts x)
	--getESEnv >>= \x -> liftES (mapM_ print $ Map.toList $ eseBelongsTo x)
	getESEnv >>= \x -> liftES (mapM_ print $ Map.toList $ eseClasses x)


t = runESM test1

main = do
        hSetBuffering stdout NoBuffering
        hSetBuffering stderr NoBuffering
	putStrLn $ "Running tes2"
	runESM test2
	putStrLn $ "Running test1 - may not converge"
	runESM test1
	return ()
