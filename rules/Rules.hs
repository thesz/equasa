{-# LANGUAGE GADTs, KindSignatures, DataKinds, FlexibleInstances, OverloadedStrings #-}

module Rules where

import qualified Data.Set as Set

import Data.String

data Side = Match | To

class NamedType a where
	typeName :: a -> String

instance NamedType Bool where typeName = const "boolean"
instance NamedType Int where typeName = const "int"
instance NamedType Integer where typeName = const "integer"
instance NamedType Double where typeName = const "double"

data Term (side :: Side) a where
	Var :: NamedType a => String -> Term side a
	Const :: a -> Term side a
	Constr :: String -> Term side a
	Bin :: BinOp a b c -> Term To a -> Term To b -> Term To c
	Un :: UnOp a b -> Term To a -> Term To b

data BinOp a b c where
	NamedBin :: String -> BinOp a a a
	Rel :: Ord a => RelOp -> BinOp a a Bool

data RelOp = RLT | RLE | REQ | RNE | RGE | RGT
data UnOp a b where
	NamedUn :: String -> UnOp a a

data Rule where
	Rule :: String -> Term Match a -> Term To b -> [Term To Bool] -> Rule

instance Num a => Num (Term To a) where
	fromInteger = Const . fromInteger
	(+) = Bin (NamedBin "+")
	(*) = Bin (NamedBin "-")
	(-) = Bin (NamedBin "-")
	abs = Un (NamedUn "abs")
	signum = Un (NamedUn "signum")

infixr 3 &&&
infixr 2 |||

class Logic a where
	lnot :: a -> a
	(&&&), (|||) :: a -> a -> a

instance Logic (Term To Bool) where
	lnot e = Un (NamedUn "not") e
	a &&& b = Bin (NamedBin "&&") a b
	a ||| b = Bin (NamedBin "||") a b

instance IsString (Term side a) where
	fromString = Var

termVars :: Term side a -> Set.Set String
termVars (Var v) = Set.singleton v
termVars (Const _) = Set.empty
termVars (Constr _) = Set.empty
termVars (Bin _ a b) = termVars a `Set.union` termVars b
termVars (Un _ a) = termVars a

rule :: String -> Term Match a -> Term To b -> [Term To Bool] -> Rule
rule ruleName match new conds
	| Set.null notDefined = Rule ruleName match new conds
	| otherwise = error $ "rule " ++ show ruleName ++ ": used, but not defined: "++show notDefined
	where
		notDefined = Set.difference used defined
		defined = termVars match
		used = Set.unions $ termVars new : map termVars conds

