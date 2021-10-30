# Tcl version of eDSL for equality saturation.
# "source equasa.tcl" to get to the API.

proc fail {msg} {
	error "fail: $msg"
}

# Creates a constructor command.
proc constr {name args} {
	if {![string is upper [string index $name 0]]} {
		fail "Constructor should start from upper case char ($name)"
	}
	proc name $args "return \[list --C $name $args]"
}

# lift a binary operation.
proc ? {a op b} {
	if {[lsearch [list == /= >= <= > < && || + - * / @] $op] < 0} {
		fail "unknown operation ($opp)"
	}
	return [list --I $a $op $b]
}

array set rules {}
proc rule {name match replace {guards {}}} {
	global rules
	if {[info exists rules($name)]} {
		fail "rule already defined ($name)"
	}
	set rules($name) [list $match $replace $guards]
}

proc var {v} {
	return [list --V $v]
}
