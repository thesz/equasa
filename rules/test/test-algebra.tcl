#!/usr/bin/tclsh

source ../equasa.tcl

# some algebra to test.

constr Add a b
constr Negate a
constr Mul a b
constr Div a b
constr Const c

rule mul_comm [Mul a b] [Mul b a]
rule add_comm [Add a b] [Add b a]

rule mul_assoc [Mul [Mul a b] c] [Mul a [Mul b c]]
rule add_assoc [Add [Add a b] c] [Add a [Add b c]]

rule mul_distr [Mul a [Add b c]] [Add [Mul a b] [Mul a c]]

rule mul_zero [Mul a [Const 0]] [Const 0]
rule mul_neut [Mul a [Const 1]] [var a]

rule add_neut [Add a [Const 0]] [var a]

rule add_neg [Add a [Negate a]] [Const 0]

rule mul_div_cancel [Mul a [Div b a]] [var b]

rule div_same [Div a a] [Const 1]

rule mul_div_distr [Mul a [Div b c]] [Div [Mul a b] c]

rule div_div [Div a [Div b c]] [Div [Mul a c] b]

