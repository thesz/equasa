# Tcl version of eDSL for equality saturation.
# "source equasa.tcl" to get to the API.

proc fail {msg} {
	puts "fail: $msg"
	exit 1
}

# Creates a constructor command.
proc constr {name args} {
	if {![string is upper [string index $name 0]]} {
		fail "Constructor should start from upper case char ($name)"
	}
	proc name $args "return \[list $name $args]"
}

# lift a binary operation.
proc ? {a op b} {
	if {[lsearch [list == /= >= <= > < && || + - * /] $op] < 0} {
		fail "unknown operation ($opp)"
	}
	return [list $a $op $b]
}
