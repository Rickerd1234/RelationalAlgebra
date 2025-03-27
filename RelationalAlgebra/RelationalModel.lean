import Mathlib.Data.Set.Basic

namespace RM

abbrev Attribute := Type

abbrev RelationName := Type

abbrev Value := Type

abbrev RelationSchema := Set Attribute

abbrev Tuple (relSch : RelationSchema) := relSch → Value

structure RelationInstance where
    schema : RelationSchema
    val : Set (Tuple schema)

abbrev DatabaseSchema := RelationName → RelationSchema

structure DatabaseInstance where
    schema : DatabaseSchema
    val : RelationName → RelationInstance
    validSchema : ∀ rel : RelationName, schema rel = (val rel).schema
