{-# LANGUAGE GADTs, TypeFamilies, UndecidableInstances, AllowAmbiguousTypes #-}

{-# OPTIONS -Wno-tabs #-}

module ES where

import Control.Applicative

import Control.Monad
import Control.Monad.State

import Data.Bits

import qualified Data.Map as Map

import Data.Maybe (fromJust)

import qualified Data.Set as Set

import Data.Typeable (Typeable, typeOf, cast, TypeRep)

import System.Environment (getArgs)
import System.Exit (exitFailure)

import System.IO

import System.IO.Unsafe

fail :: String -> IO ()
fail m = do
	hPutStrLn stderr m
	exitFailure

trace :: String -> a -> a
trace msg x = unsafePerformIO $ do { putStrLn msg; return x }
traceM :: Monad m => String -> m ()
traceM msg = (unsafePerformIO $ do { putStrLn msg; }) `seq` return ()

notImpl :: String -> a
notImpl s = error ("not implemented: " ++ s)

internal :: String -> a
internal s = error $ "Internal error: " ++ s

-- non-negative values are for facts' references, negative ones are variables in matches.
newtype ID = ID { idIndex :: Int } deriving (Eq, Ord)

__, ignore :: ID
ignore = ID (-1)
__ = ignore

genMatchVars :: [ID]
genMatchVars = map ID [-2,-3..]

class Show mp => PatResult mp where
	getQuery :: mp -> [(ID, Hold)]
	fromQueryResult :: [(ID, Hold)] -> mp

instance PatResult () where
	getQuery () = []
	fromQueryResult [] = ()

instance Fact f => PatResult (ID, f) where
	getQuery (a, f) = [(a, Hold f)]
	fromQueryResult [(a, Hold f)] = fromJust $ do
		x <- cast f
		return (a, x)
instance (Fact f1, Fact f2) => PatResult ((ID, f1), (ID, f2)) where
	getQuery ((a1, f1), (a2, f2)) = [(a1, Hold f1), (a2, Hold f2)]
	fromQueryResult [(a1, Hold f1), (a2, Hold f2)] = fromJust $ do
		x1 <- cast f1
		x2 <- cast f2
		return ((a1, x1), (a2, x2))
instance (Fact f1, Fact f2, Fact f3) => PatResult ((ID, f1), (ID, f2), (ID, f3)) where
	getQuery ((a1, f1), (a2, f2), (a3, f3)) = [(a1, Hold f1), (a2, Hold f2), (a3, Hold f3)]
	fromQueryResult [(a1, Hold f1), (a2, Hold f2), (a3, Hold f3)] = fromJust $ do
		x1 <- cast f1
		x2 <- cast f2
		x3 <- cast f3
		return ((a1, x1), (a2, x2), (a3, x3))

instance (Fact f1, Fact f2, Fact f3, Fact f4) => PatResult ((ID, f1), (ID, f2), (ID, f3), (ID, f4)) where
	getQuery ((a1, f1), (a2, f2), (a3, f3), (a4, f4)) = [(a1, Hold f1), (a2, Hold f2), (a3, Hold f3), (a4, Hold f4)]
	fromQueryResult [(a1, Hold f1), (a2, Hold f2), (a3, Hold f3), (a4, Hold f4)] = fromJust $ do
		x1 <- cast f1
		x2 <- cast f2
		x3 <- cast f3
		x4 <- cast f4
		return ((a1, x1), (a2, x2), (a3, x3), (a4, x4))


checkQuery :: PatResult q => q -> a -> a
checkQuery query x = check (getQuery query)
	where
		check [] = x
		check ((id,h) : idhs)
			-- all binds:
			| all (<ID 0) (id : getIDs h) = check idhs
			-- some are not bound.
			| otherwise = error $ "invalid match " ++ show (id,h) ++ " in " ++ show query

sameType :: Hold -> Hold -> Bool
sameType (Hold f1) (Hold f2) = case cast f2 of
	Just f2'
		| x <- asTypeOf f1 f2' -> True
	_ -> False
bindInMatch :: (Monad m) => (ID, Hold) -> (ID,Hold) -> ESM m (FromID IDSet)
bindInMatch (matchID, matchH) (checkID, checkH)
	| sameType matchH checkH = do
		ese <- get
		let	normCheckID = normID ese checkID
			normCheckH = norm ese checkH
			binds' = zip (matchID : getIDs matchH) (map Set.singleton $ normCheckID : getIDs normCheckH)
			binds = filter ((<ignore) . fst) binds'
			bindsMap = Map.fromListWith Set.union binds
			goodBinds = all ((==1) . Set.size) bindsMap
		return $ if goodBinds then Map.fromList binds else Map.empty
	| otherwise = return Map.empty

type MQ q r = (String, q, q -> Maybe (r, (ID, ID)))
match :: (Monad m, PatResult q, PatResult r) => (String, q, q -> Maybe (r, (ID, ID))) -> ESM m ()
match (name, query, act) = checkQuery query $ do
	--traceM $ "=============================\n== rule " ++ show name
	ese <- get
	let	idhs = Set.toList $ Set.fromList [ (normID ese i, norm ese f) | (i,f) <- Map.toList (eseIDFacts ese)]
	sets <- collectBinds Map.empty idhs
	--traceM ("query: " ++ show query)
	--traceM ("sets: " ++ show sets)
	let	allSets = Map.foldr (Map.unionWith Set.union) Map.empty sets
		reducedSets = Map.foldr (\a b -> Map.differenceWith (\a b -> Just $ Set.intersection a b) b a) allSets sets
	--traceM $ "all sets: " ++ show allSets
	--traceM ("reduced binds: " ++ show reducedSets)
	matches <- collectMatches reducedSets Map.empty idhs
	--traceM $ "matches: " ++ show matches
	let	tuples' = if Map.size matches == length holdQuery
			then filterJoined $ genTuples $ Map.toList $ Map.map Set.toList matches
			else []
		changed = eseChanged ese
		tuples = filter (any (`Set.member` changed) . concatMap (\(i,h) -> i : getIDs h)) tuples' 
	traceM $ show (length tuples) ++ " tuples generated"
	--traceM $ "first not more than 10 tuples: " ++ show (take 10 tuples)
	apply tuples
	where
		holdQuery = getQuery query
		indexedHoldQuery = zip [0..] holdQuery
		collectBinds !binds [] = return binds
		collectBinds !binds (idh:idhs) = do
			inc <- collectQueryBinds Map.empty indexedHoldQuery idh
			collectBinds (Map.unionWith (Map.unionWith Set.union) binds inc) idhs
		collectQueryBinds binds [] _ = return binds
		collectQueryBinds binds ((i, ih):ihs) idfact = do
			inc <- bindInMatch ih idfact
			collectQueryBinds (Map.insertWith (Map.unionWith Set.union) i inc binds) ihs idfact
		collectMatches allowedBinds matches [] = return matches
		collectMatches allowedBinds matches (idh:idhs) = do
			--traceM $ "collecting matches on fact " ++ show idh
			inc <- collectQueryMatches allowedBinds Map.empty idh indexedHoldQuery
			collectMatches allowedBinds (Map.unionWith Set.union inc matches) idhs
		collectQueryMatches allowedBinds matches idfact [] = return matches
		collectQueryMatches allowedBinds matches idfact ((i, ih) : ihs) = do
			binds' <- bindInMatch ih idfact
			--traceM $ "  binds' for " ++ show (i, ih) ++ ": " ++ show binds'
			let	binds = Map.intersectionWith Set.intersection binds' allowedBinds
				good = not (Map.null binds) && all (not . Set.null) binds
				matches'
					| good = Map.insertWith Set.union i (Set.singleton idfact) matches
					| otherwise = matches
			--traceM $ "  binds: " ++ show binds ++ " " ++ (if good then "good" else "not good")
			collectQueryMatches allowedBinds matches' idfact ihs
		genTuples :: [(Int, [a])] -> [[a]]
		genTuples [] = [[]]
		genTuples ((_,xs):xss) = concatMap (\x -> map (x:) $ genTuples xss) xs
		apply [] = return ()
		apply (tuple:tuples) = do
			--traceM $ "tuple " ++ show tuple
			--let	f h t = do
			--		traceM $ "before bindInMatch " ++ show t ++ " " ++ show h
			--		bs <- bindInMatch h t
			--		traceM $ "bs " ++ show bs
			--		let	fromSingleton xs = case Set.toList xs of
			--				[x] -> x
			--				_ -> internal $ "not a singleton: " ++ show xs
			--		return $ Map.map fromSingleton bs
			--	mustEqual a b
			--		| a /= b = internal $ "not equal"
			--		| otherwise = a
			--appliedBindsList <- zipWithM f holdQuery tuple
			--let	appliedBinds = Map.unionsWith mustEqual appliedBindsList
			--traceM $ "applied binds: " ++ show appliedBinds
			let	q = fromQueryResult tuple
				new = act q
			--traceM $ "new: " ++ show new
			let	storeBind binds [] = return binds
				storeBind binds ((x,h):xhs) = do
					--traceM $ "current binds " ++ show binds
					let	is = getIDs h
						boundIS = [Map.findWithDefault j j binds | j <- is]
						bad = filter (<=ignore) boundIS
					when (not $ null bad) $ internal $ "cannot bind " ++ show bad ++ " in " ++ show h
					let	h' = changeIDs h boundIS
					r <- case h' of
						Hold f -> do
							add f
					--traceM $ "added " ++ show h' ++ " as " ++ show r
					when (x>= ignore) $ internal $ "cannot bind result to invalid var " ++ show x
					--traceM $ "binding " ++ show x ++ " to " ++ show r
					storeBind (Map.insert x r binds) xhs
			case new of
				Just (r, (a,b)) -> do
					let	rq = getQuery r
					bs <- storeBind Map.empty rq
					let	chg j
							| j == ignore = internal $ "ignore in eqiality " ++ show (a,b)
							| j < ignore = Map.findWithDefault (internal $ "unable to find bind for " ++ show j) j bs
							| otherwise = j
						a' = chg a
						b' = chg b
					a' === b'
				Nothing -> return ()
			apply tuples
		filterJoined :: [[(ID, Hold)]] -> [[(ID, Hold)]]
		filterJoined hss = filter isJoined hss
			where
				flattenBinds = concatMap (\(i,h) -> i : getIDs h)
				queryBinds = flattenBinds holdQuery
				isJoined tuple = and $ map fst $ scanl chk (True, Map.empty) $ zip queryBinds $ flattenBinds tuple
				chk (False, x) (toBind, what) = (False, x)
				chk (True, binds) (toBind, what)
					| toBind == ignore = (True, binds)
					| otherwise = case Map.lookup toBind binds of
						Just bound
							| bound == what -> (True, binds)
							| otherwise -> (False, binds)
						Nothing -> (True, Map.insert toBind what binds)

instance Show ID where
	showsPrec p (ID x) = ((o ++ "ID " ++ show x ++ c) ++)
		where
			(o,c) = if p >= 10 then ("(", ")") else ("", "");

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
		, eseNewChanged	:: !IDSet
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
	, eseNewChanged		= Set.empty
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
		h = Hold normFact
		--nh = Hold normFact
		newIndex = eseIndex ese
		newID = ID newIndex
		mbOldID = Map.lookup h $ eseFactIDs ese
	case mbOldID of
		Just id -> return $ Map.findWithDefault undefined id $ eseBelongsTo ese
		Nothing -> do
			--trace ("add: " ++ show (fact, normFact, mbOldID, newID)) (return ())
			let	refd = Map.fromListWith Set.union [(ref, Set.singleton newID) | ref <- refs]
			put $ ese
				{ eseIndex = newIndex + 1
				, eseFactIDs = Map.insert h newID $ eseFactIDs ese
				, eseIDFacts = Map.insert newID h $ eseIDFacts ese
				, eseBelongsTo = Map.insert newID newID $ eseBelongsTo ese
				, eseClasses = Map.insert newID (Set.singleton newID) $ eseClasses ese
				, eseNewChanged = Set.insert newID $ eseNewChanged ese
				, eseReferredBy = Map.unionWith Set.union refd $ eseReferredBy ese
				}
			return newID

(===) :: Monad m => ID -> ID -> ESM m ()
ida' === idb'
	| ida' == idb' = return ()	-- trivial case.
	| otherwise = do
		ese <- get
		let	ida = Map.findWithDefault undefined ida' $ eseBelongsTo ese
			idb = Map.findWithDefault undefined idb' $ eseBelongsTo ese
			cls = min ida idb
			memb = max ida idb
		let	members c = do
				return $ Map.findWithDefault (Set.singleton c) c $ eseClasses ese
		cms <- members cls
		mms <- members memb
		let	both = Set.union cms mms
			m = Map.fromSet (const cls) both
		if both == cms
			then return ()
			else do
				--trace ("new eq class: " ++ show cls ++ " === " ++ show both) ( return ())
				--trace ("            : " ++ show (ida', idb', ida, idb)) ( return ())
				modify $ \ese -> ese
					{ eseClasses = Map.insert cls both $ Map.delete memb $ eseClasses ese
					, eseBelongsTo = Map.union m $ eseBelongsTo ese
					, eseNewChanged = Set.insert cls $ eseNewChanged ese
					}
	where

fetch :: (Fact f, Monad m) => ID -> ESM m (Maybe f)
fetch i = do
	castHold . Map.findWithDefault (internal $ "unknown ID: " ++ show i) i . eseIDFacts <$> get

changes :: Monad m => IDSet -> Int -> ESM m (Map.Map Int IDSet)
changes start height = do
	(m, _) <- acc height
	ese <- get
	return $ Map.map (chg ese) m
	where
		chg ese s = Map.foldr Set.insert Set.empty ids
			where
				m = Map.fromSet (const ()) s :: FromID ()
				hs = Map.elems $ flip Map.intersection m $ eseIDFacts ese
				hs' = map (norm ese) hs :: [Hold]
				m' = Map.fromList [(x,()) | x <- hs'] :: Map.Map Hold ()
				ids = flip Map.intersection m' $ eseFactIDs ese :: Map.Map Hold ID
				
		acc height
			| height < 1 = return (Map.singleton 0 start, start)
			| otherwise = do
				(m', s) <- acc (height - 1)
				let	m = Map.fromSet (const ()) s
				ese <- get
				let	ss = flip Map.intersection m $ eseReferredBy ese
					s' = Map.foldr Set.union s ss
				return (Map.insert height s' m', s')

type Rule m = IDSet -> ESM m ()
data NamedRule m = NamedRule { ruleName :: String, ruleRule :: Rule m, ruleHeight :: Int }

runRules :: Monad m => [NamedRule m] -> ESM m ()
runRules namedRules = do
	ese <- get
	let	start = eseChanged ese
	if Set.null start
		then return ()
		else do
			trace ("equalities changes: " ++ show start) (return ())
			modify $ \ese -> ese { eseNewChanged = Set.empty }
			let	maxHeight = maximum $ map ruleHeight namedRules
			starts <- changes start maxHeight
			forM_ namedRules $ \(NamedRule name r height) -> do
				trace ("running rule " ++ show name) (return ())
				r $ Map.findWithDefault (internal $ "no start for height " ++ show height) height starts
			runRules namedRules

namedRule :: Monad m => String -> Int -> Rule m -> NamedRule m
namedRule s h r = NamedRule s r h

onID :: (Fact f, Monad m) => ID -> ((ID, f) -> ESM m ()) -> ESM m ()
onID i act = do
	ese <- get
	let	bt = Map.findWithDefault (internal $ "no class for " ++ show i) i $ eseBelongsTo ese
		ids = Set.toList $ Map.findWithDefault (Set.singleton i) bt $ eseClasses ese
	forM_ ids $ \id -> do
		let	y = norm ese $ Map.findWithDefault (internal $ show id ++ " not found") id $ eseIDFacts ese
		case y of
			Hold x -> case cast x of
				Just f -> act (id, f)
				Nothing -> return ()
onIDs :: (Fact f, Monad m) => IDSet -> ((ID, f) -> ESM m ()) -> ESM m ()
onIDs idset act = do
	forM_ (Set.toList idset) (flip onID act)

whenEqual :: Monad m => ID -> ID -> ESM m () -> ESM m ()
whenEqual a b act = do
	ese <- get
	let	find c = Map.findWithDefault (internal $ "no equality class for " ++ show c) c $ eseBelongsTo ese
		ac = find a
		bc = find b
	when (ac == bc) act

getESEnv :: Monad m => ESM m ESEnv
getESEnv = get

liftES :: Monad m => m a -> ESM m a
liftES g = ESM (lift g)


