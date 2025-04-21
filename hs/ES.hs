-- |ES.hs
--
-- Equality saturation (hence ES) engine that allows for separation of concerns.
--
-- The facts in the database are represented by different types. E.g., constant
-- True and False are represented by "data FTrue = FTrue" and "data FFalse = FFalse",
-- variables can be represented by "data Var = Var String", operations by "data Negate = Negate ID"
-- and "data Plus = Plus ID ID". Each such fact can be added and matched
-- independently, facilitating modular development. For example, one can implement
-- expression optimizations independently from implementation of ISA mapping.
--
-- Copyright (C) 2025 Serguey Zefirov.
--
-- Licensed under 2-clause BSD license, reproduced below.
--
-- Redistribution and use in source and binary forms, with or without modification,
-- are permitted provided that the following conditions are met:
-- 1. Redistributions of source code must retain the above copyright notice, this
--    list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright notice, this
--    list of conditions and the following disclaimer in the documentation and/or other
--    materials provided with the distribution.
--
-- THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR
-- IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
-- AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR
-- CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
-- CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
-- ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
-- NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
-- ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

{-# LANGUAGE GADTs, TypeFamilies, UndecidableInstances, AllowAmbiguousTypes #-}

{-# OPTIONS -Wno-tabs #-}

module ES where

import Debug.Trace

import Control.Applicative

import Control.Monad
import Control.Monad.State

import Data.Bits

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Typeable (Typeable, typeOf, cast, TypeRep)

import System.Environment (getArgs)
import System.Exit (exitFailure)

import System.IO

fail :: String -> IO ()
fail m = do
	hPutStrLn stderr m
	exitFailure

notImpl :: String -> a
notImpl s = error ("not implemented: " ++ s)

internal :: String -> a
internal s = error $ "Internal error: " ++ s

newtype ID = ID { idIndex :: Int } deriving (Eq, Ord, Show)

class (Show f, Ord f, Eq f, Typeable f) => Fact f where
	getIDs :: f -> [ID]
	changeIDs :: f -> [ID] -> f

data Hold where Hold :: Fact f => f -> Hold
deriving instance Show Hold

castHold :: Typeable a => Hold -> Maybe a
castHold (Hold x) = cast x

instance Fact Hold where
	getIDs (Hold f) = getIDs f
	changeIDs (Hold f) ids = Hold $ changeIDs f ids

instance Eq Hold where Hold a == Hold b = cast a == Just b
instance Ord Hold where
	compare (Hold a) (Hold b) = case cast a of
		Just a' -> compare a' b
		Nothing -> compare (typeOf a) (typeOf b)

type FromID a = Map.Map ID a
type ToID a = Map.Map a ID
type IDSet = Set.Set ID
data ESEnv =
	ESEnv	{ eseIndex	:: !Int
		, eseClasses	:: !(FromID IDSet)	-- keys are least elements of values, otherwise values are not present.
		, eseChanged	:: !IDSet
		, eseBelongsTo	:: !(FromID ID)	-- class to which key belongs.
		, eseFactIDs	:: !(ToID Hold)
		, eseIDFacts	:: !(FromID Hold)
		, eseReferredBy	:: !(FromID IDSet)
		}
		deriving (Show)

startESEnv :: ESEnv
startESEnv = ESEnv
	{ eseIndex		= 0
	, eseClasses		= Map.empty
	, eseChanged		= Set.empty
	, eseBelongsTo		= Map.empty
	, eseFactIDs		= Map.empty
	, eseIDFacts		= Map.empty
	, eseReferredBy		= Map.empty
	}

newtype ESM m a = ESM { esmStateTransform :: StateT ESEnv m a}

runESM :: Monad m => ESM m a -> m a
runESM (ESM act) = evalStateT act startESEnv

instance Functor (ESM m) where
	fmap f a = f <$> a
instance Monad m => Applicative (ESM m) where
	pure a = ESM (return a)
	liftA2 f (ESM a) (ESM b) = ESM (do { x <- a; y <- b; return (f x y)})
deriving instance Monad m => Monad (ESM m)
deriving instance Monad m => MonadState ESEnv (ESM m )

normID :: ESEnv -> ID -> ID
normID ese id = case Map.lookup id (eseBelongsTo ese) of
	Just id' -> id'
	_ -> internal $ "id not found: " ++ show (idIndex id)

norm :: Fact f => ESEnv -> f -> f
norm ese f = changeIDs f $ map (normID ese) $ getIDs f

add :: (Fact f, Monad m) => f -> ESM m ID
add fact = do
	ese <- get
	let	tyrep = typeOf fact
		refs = getIDs fact
		normRefs = map (normID ese) refs
		normFact = changeIDs fact normRefs
		h = Hold fact
		newIndex = eseIndex ese
		newID = ID newIndex
	case Map.lookup h $ eseFactIDs ese of
		Just id -> return id
		Nothing -> do
			let	refd = Map.fromListWith Set.union [(ref, Set.singleton newID) | ref <- refs]
			put $ ese
				{ eseIndex = newIndex + 1
				, eseFactIDs = Map.insert h newID $ eseFactIDs ese
				, eseIDFacts = Map.insert newID h $ eseIDFacts ese
				, eseBelongsTo = Map.insert newID newID $ eseBelongsTo ese
				, eseClasses = Map.insert newID (Set.singleton newID) $ eseClasses ese
				, eseChanged = Set.insert newID $ eseChanged ese
				, eseReferredBy = Map.unionWith Set.union refd $ eseReferredBy ese
				}
			return newID

(===) :: Monad m => ID -> ID -> ESM m ()
ida === idb
	| ida == idb = return ()	-- trivial case.
	| otherwise = do
		let	members c = do
				ese <- get
				return $ Map.findWithDefault (internal $ "unknown class " ++ show c) c $ eseClasses ese
		cms <- members cls
		mms <- members memb
		let	both = Set.union cms mms
			m = Map.fromSet (const cls) both
		modify $ \ese -> ese
			{ eseClasses = Map.insert cls both $ Map.delete memb $ eseClasses ese
			, eseBelongsTo = Map.union m $ eseBelongsTo ese
			}
	where
		cls = min ida idb
		memb = max ida idb

fetch :: (Fact f, Monad m) => ID -> ESM m (Maybe f)
fetch i = do
	castHold . Map.findWithDefault (internal $ "unknown ID: " ++ show i) i . eseIDFacts <$> get

changes :: Monad m => IDSet -> Int -> ESM m IDSet
changes start height = do
	s <- acc height
	let	m = Map.fromSet (const ()) s :: FromID ()
	ese <- get
	let	hs = Map.elems $ flip Map.intersection m $ eseIDFacts ese
		hs' = map (norm ese) hs :: [Hold]
		m' = Map.fromList [(x,()) | x <- hs'] :: Map.Map Hold ()
		ids = flip Map.intersection m' $ eseFactIDs ese :: Map.Map Hold ID
	return $ Map.foldr Set.insert Set.empty ids
	where
		acc height
			| height < 1 = return start
			| otherwise = do
				s <- acc (height - 1)
				let	m = Map.fromSet (const ()) s
				ese <- get
				let	ss = flip Map.intersection m $ eseReferredBy ese
				return $ Map.foldr Set.union s ss

type Rule m = IDSet -> ESM m ()
type NamedRule m = (String, Rule m)
runRules :: Monad m => [NamedRule m] -> ESM m ()
runRules namedRules = do
	ese <- get
	let	start = eseChanged ese
	if Set.null start
		then return ()
		else do
			modify $ \ese -> ese { eseChanged = Set.empty }
			forM_ namedRules $ \(n, r) -> do
				r start
			runRules namedRules

onID :: (Fact f, Monad m) => ID -> ((ID, f) -> ESM m ()) -> ESM m ()
onID i act = do
	ese <- get
	let	y = Map.findWithDefault (internal $ show i ++ " not found") i $ eseIDFacts ese
	case y of
		Hold x -> case cast x of
			Just f -> act (i, f)
			Nothing -> return ()
onIDs :: (Fact f, Monad m) => IDSet -> ((ID, f) -> ESM m ()) -> ESM m ()
onIDs idset act = do
	forM_ (Set.toList idset) (flip onID act)

getESEnv :: Monad m => ESM m ESEnv
getESEnv = get

liftES :: Monad m => m a -> ESM m a
liftES g = ESM (lift g)
