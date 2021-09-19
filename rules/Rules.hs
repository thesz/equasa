module Rules where

type Name = String

data Type =
		Prim	Name
	|	Alg	Name	[(Name, [Type])
	|	Func	Type	Type
	deriving (Eq, Ord, Show)

type NameType = (Name, Type)

data Term =
		Var	NameType
	|	Constr	NameType	[Term]
	deriving (Eq, Ord, Show)

data Rule = Rule	Term	Term	[Term]
	deriving (Eq, Ord, Show)
