import Mathlib.Data.Set.Basic

namespace RM

abbrev Attribute := Type

abbrev RelationName := Type

abbrev Value := Type

abbrev RelationSchema := Set Attribute

structure Tuple where
    schema : RelationSchema
    val : schema → Value

structure RelationInstance where
    schema : RelationSchema
    tuples : Set Tuple
    validSchema : ∀ t ∈ tuples, t.schema = schema

abbrev DatabaseSchema := RelationName → RelationSchema

structure DatabaseInstance where
    schema : DatabaseSchema
    relations : RelationName → RelationInstance
    validSchema : ∀ rel : RelationName, schema rel = (relations rel).schema
