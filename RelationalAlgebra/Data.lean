import Mathlib.Data.Set.Basic
open Lean List

-- Define Attribute as a name
abbrev Attribute := String

-- Define Relation as a name
abbrev Relation := String

-- Define a Value type for possible attribute values
inductive Value
  | Int : Int → Value
  | Str : String → Value
  | Bool : Bool → Value
  | Null : Value
  deriving Repr, BEq

-- Define a Domain as a function that checks if a value is valid
abbrev Domain := Value → Bool

-- Define domains for attributes
def intDomain : Domain
  | .Int _ => true
  | _ => false

def int?Domain : Domain
  | .Int _ => true
  | .Null => true
  | _ => false

def strDomain : Domain
  | .Str _ => true
  | _ => false

def mixDomain : Domain
  | .Str _ => true
  | .Int _ => true
  | _ => false

-- A Relation Schema is a finite set of attributes with associated domains
structure RelationSchema where
  attributes : List (Attribute × Domain)
  nodup : Nodup (attributes.map Prod.fst)

def RelationSchema.isValidValuePair (sch : RelationSchema) (AV : Attribute × Value) : Bool :=
  ((sch.attributes.lookup AV.fst).getD (λ _ ↦ false)) AV.snd

-- A Tuple for a given Relation Schema
structure Tuple (schema : RelationSchema) where
  values : List (Attribute × Value)
  nodup : Nodup (values.map Prod.fst)
  inSchema : ∀ AV, AV ∈ values → schema.isValidValuePair AV
  coverSchema : ∀ rel, rel ∈ schema.attributes → rel.fst ∈ (values.map Prod.fst)

-- A Relation Instance is a finite set of tuples that conform to a relation type
abbrev RelationInstance (relSchema : RelationSchema) := Set (Tuple relSchema)

-- A Database Schema assigns relation schemas to relation names
structure DatabaseSchema where
  relations : List (Relation × RelationSchema)
  nodup : Nodup (relations.map Prod.fst)

-- A Database Instance assigns relation instances to relation names, ensuring schema conformance
abbrev DependentRelationInstanceType (dbSch : DatabaseSchema) := (Σ name : Relation, (((dbSch.relations.lookup name).map RelationInstance).getD Unit))

structure DatabaseInstance (dbSch : DatabaseSchema) where
  relations : List (DependentRelationInstanceType dbSch)
  nodup : Nodup (relations.map Sigma.fst)
  inSchema : ∀ rel, rel ∈ relations → (dbSch.relations.lookup rel.fst).isSome
  coverSchema : ∀ rel, rel ∈ dbSch.relations → rel.fst ∈ (relations.map Sigma.fst)
