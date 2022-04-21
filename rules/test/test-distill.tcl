#!/usr/bin/tclsh

source ../equasa.tcl

# an attempt to implement distillation.

# booleans.
constr True
constr False

# lists.
constr Cons Ref Ref
constr Nil

# triple for case match
# (String, [String], Term)
constr Triple String Ref Ref

# terms.
# data Term =
#        Free String
constr Free String
#      | Bound Int
constr Bound Int
#      | Lambda String Term
constr Lambda String Ref
#
constr Con String Ref
#
constr Apply Ref Ref
constr Fun String
constr Case Ref Ref
constr Let String Ref Ref

# programs.
# type Prog = (Term, [(String,([String], Term))])
constr Prog Ref Ref

