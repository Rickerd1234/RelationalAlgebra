import Mathlib.Data.Set.Basic

namespace RM

-- abbrev Attribute := DecidableEq Type

-- abbrev RelationName := DecidableEq Type

-- abbrev Value := DecidableEq Type

inductive Attribute
| Name | Age | Salary
deriving DecidableEq

inductive RelationName
| Employee | Department
deriving DecidableEq

abbrev Value := String

abbrev RelationSchema := Set Attribute

abbrev Tuple (relSch : RelationSchema) := relSch → Value

abbrev RelationInstance (relSch : RelationSchema) := Set (Tuple relSch)

abbrev DatabaseSchema := RelationName → RelationSchema

abbrev DatabaseInstance (dbSch : DatabaseSchema) := (rel : RelationName) → RelationInstance (dbSch rel)
