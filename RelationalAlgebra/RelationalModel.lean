import Mathlib.Data.Set.Basic
import Mathlib.Data.PFun

namespace RM

abbrev Attribute := Type

abbrev RelationName := Type

abbrev Value := Type

abbrev RelationSchema := Set Attribute

abbrev Tuple := Attribute →. Value

structure RelationInstance where
    schema : RelationSchema
    tuples : Set Tuple
    validSchema : ∀ t : Tuple, t ∈ tuples → t.Dom = schema

abbrev DatabaseSchema := RelationName → RelationSchema

structure DatabaseInstance where
    schema : DatabaseSchema
    relations : RelationName → RelationInstance
    validSchema : ∀ rel : RelationName, schema rel = (relations rel).schema
