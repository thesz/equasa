# Tcl version of eDSL for equality saturation.
# "source equasa.tcl" to get to the API.

proc fail {msg} {
	error "fail: $msg"
}

# what types we know?
array set _known_types {
	Ref [list "reference to other fact" ]
	Int [list "integer, 64 bit" ]
	Double [list "double precision floating point" ]
}
proc _known_type {type} {
	global _known_types
	if {[info exists _known_types($type)]} {
		return
	}
	fail "unknown type ($type)"
}

# Creates a constructor command.
# Constructors should have types in constr command.
array set _constructors {}
proc constr {name args} {
	global _constructors
	if {[info exists _constructors($name)]} {
		fail "constructor redefined ($name)"
	}
	set _constructors($name) $args
	if {![string is upper [string index $name 0]]} {
		fail "Constructor should start from upper case char ($name)"
	}
	set vi 1
	set vars [list ]
	foreach ty $args {
		_known_type $ty
		lappend vars v$vi
	}
	proc $name $vars "return \[list --C $name $vars]"
}

# lift a binary operation.
proc ? {a op b} {
	if {[lsearch [list == /= >= <= > < && || + - * / @] $op] < 0} {
		fail "unknown operation ($opp)"
	}
	return [list --I $a $op $b]
}

array set _rules {}
proc rule {name match replace {guards {}}} {
	global _rules
	if {[info exists _rules($name)]} {
		fail "rule already defined ($name)"
	}
	set _rules($name) [list $match $replace $guards]
}

proc var {v} {
	return [list --V $v]
}

# -----------------------------------------------------------------------------
# Generate saturation code.

proc _gen_sql_def_value {type} {
	switch -- $type {
		integer { return 0 }
		double { return 0.0}
	}
	fail "unknown type ($type)"
}
proc _gen_sql_schema {} {
	global _constructors
	set field_constraint [list "" ""]
	set field_type [list "integer" "integer" ]
	set table_field [list "index" "tag"]
	array set fields_added {}
	foreach {constr types} [array get _constructors] {
		set index 1
		foreach type $types {
			set field_name ${type}_$index
			if {![info exists fields_added($field_name)]} {
				lappend table_field $field_name
				lappend field_constraint
				set fields_added($field_name) ""
			}
			incr index
		}
	}
	set create "CREATE TABLE terms\n"
	set prefix "( "
	foreach name $table_field type $field_type constr $field_constraint {
		append create $prefix $name " " $type
		if {[string length $constr] > 0} {
			append create " " $constr
		}
		append create "\n"
		set prefix ", "
	}
	append create ");\n"
	return $create
}
proc _gen_sql {subtarget} {
	set schema [_gen_sql_schema]
	return [list schema $schema]
}

proc gen {target {subtarget tcl}} {
	switch -- $target {
		sql {
			_gen_sql $subtarget
		}
		* {
			fail "target unknown ($target)"
		}
	}
}
