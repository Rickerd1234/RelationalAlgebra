import Mathlib.Data.Set.Basic
import Mathlib.Data.FinSet.Defs

-- Alias for collection to easily try different types
abbrev Collection := Array

-- Variable part of the relational model
inductive Attribute where
  | a1
  | a2
  | a3
  | b1
  | b2
  | b3

inductive Relation where
  | R
  | S

abbrev ValueType := Option String


-- Types for the general relational model
abbrev RelationSchema := Collection Attribute

abbrev TupleValues := Collection ValueType

abbrev Tuple := Attribute → ValueType

abbrev RelationInstance := Collection Tuple



-- Instances for the relational model
def r1 : RelationSchema := #[.a1, .a3, .b1]

def t1 : Tuple
  | .a1 => some "123"
  | .a2 => some "abc"
  | .a3 => some "true"
  | _ => none

def data : RelationInstance := #[
  t1,
  fun
  | .a1 => "example"
  | .a2 => "text"
  | .a3 => "more text"
  | _ => none,
  fun
  | .a1 => "124"
  | .a2 => "abd"
  | .a3 => "false"
  | _ => none
]


-- Experimental code to test relational model
def tExec (t : Tuple) (as : RelationSchema) :=
  as.foldl (λ agg att ↦ agg.push (t att)) #[]

def riExec (ts : Collection Tuple) (rs : RelationSchema) : Collection TupleValues :=
  ts.foldl (λ agg t ↦ agg.push (tExec t rs)) #[]

#eval riExec data r1
#check riExec data r1
