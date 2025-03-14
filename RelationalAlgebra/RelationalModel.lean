import Mathlib.Data.Set.Basic

namespace RM

abbrev Attribute := Type

abbrev RelationName := Type

abbrev Value := Type

abbrev RelationSchema := Set Attribute

abbrev Tuple (relSch : RelationSchema) := relSch → Value

abbrev RelationInstance (relSch : RelationSchema) := Set (Tuple relSch)

abbrev DatabaseSchema := RelationName → RelationSchema

abbrev DatabaseInstance (dbSch : DatabaseSchema) := (rel : RelationName) → RelationInstance (dbSch rel)
