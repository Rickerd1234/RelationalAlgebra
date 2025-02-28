import Mathlib.Data.Set.Basic

abbrev Attribute := Type

abbrev RelationName := Type

abbrev Value := Option Type

abbrev RelationSchema := Set Attribute

structure Tuple (relSch : RelationSchema) where
  val : Attribute → Value
  inSchema : ∀ a ∈ relSch, (val a).isSome

abbrev RelationInstance (relSch : RelationSchema) := Set (Tuple relSch)

abbrev DatabaseSchema := RelationName → RelationSchema

abbrev DatabaseInstance (dbSch : DatabaseSchema) := (rel : RelationName) → RelationInstance (dbSch rel)
