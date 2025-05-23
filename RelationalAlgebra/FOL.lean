import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Util

open RM

-- Types for FOL queries
section types

abbrev Variable := String

inductive Term
  | const (c : Value) : Term
  | var (v : Variable) : Term

inductive Atom
  | Eq : Term → Term → Atom

abbrev AttributeAssignment := Attribute →. Term

inductive Formula
  | R       : RelationName → AttributeAssignment → Formula
  | Op      : Atom → Formula
  | And     : Formula → Formula → Formula
  -- | Or      : Formula → Formula → Formula
  -- | Not     : Formula → Formula
  | Ex      : Variable → Formula → Formula
  -- | All     : Variable → Formula → Formula

end types


-- Definitions for evaluating FOL queries
section evaluate

abbrev VariableAssignment := Variable →. Value

abbrev VariableProjection := Variable →. Attribute

-- Active domain restriction for the database instance
def Dom (DB : DatabaseInstance) : Set Value :=
  {v |                              -- All values for which
    ∃ rn : RelationName,            -- Exists a relation name
    ∃ t ∈ (DB.relations rn).tuples, -- Exists a tuple in the corresponding relation instance tuples
    ∃ a : Attribute,                -- Exists an attribute
      t.Dom a →                     -- If the attribute is in the domain
        t a = some v                -- Then the value is the result of this tuple-attribute evaluation
  }

-- Extract values from Term, based on VariableAssignment
def getTerm : VariableAssignment → Term →. Value
  | _,  .const c => c
  | VA, .var v   => VA v

-- Verify whether a VariableAssignment and AttributeAssignment is satisfied by the Tuple
def satisfies_tpl : VariableAssignment → AttributeAssignment → Tuple → Prop
  | VA, AA, T =>
      ∀ att ∈ T.Dom,                    -- Where for all attributes in the schema
      ∃ trm : Term,                     -- There exists a term
        AA.Dom att →                    -- If attribute is assigned in the formula
          AA att = some trm ∧           -- Then this assigned term
          getTerm VA trm = T att        -- Should match the value for this attribute in the tuple

-- Verify whether a Formula.R (VariableAssignment and AttributeAssignment) is satisfied by the DatabaseInstance
def satisfies_rel : VariableAssignment → RelationInstance → AttributeAssignment → Prop
  | VA, R, AA =>
      ∃ tpl ∈ R.tuples,                 -- There exists a tuple in the relation
        satisfies_tpl VA AA tpl         -- Which satisfies the formula for the variable and attribute assignment

-- Verify whether a Formula.Op is satisfied
def satisfies_op : VariableAssignment → Atom → Prop
  | VA, .Eq t1 t2 => getTerm VA t1 = getTerm VA t2

-- Assign a variable
def VarAssign : VariableAssignment → Variable → Value → VariableAssignment
  | VA, var, val => λ x => ite (var == x) val (VA x)

-- Check whether a VariableAssignment satisfies a Formula for specified DatabaseInstance
def SatisfiesRec : VariableAssignment → Formula → DatabaseInstance → Prop
  | VA, .R rn aa,   DB => satisfies_rel VA (DB.relations rn) aa
  | VA, .Op a,      _  => satisfies_op VA a
  | VA, .And l r,   DB => SatisfiesRec VA l DB ∧ SatisfiesRec VA r DB
  -- | VA, .Or l r,    DB => SatisfiesRec VA l DB ∨ SatisfiesRec VA r DB
  -- | VA, .Not f,     DB => SatisfiesRec VA f DB
  | VA, .Ex v f,    DB => (∃z ∈ Dom DB, SatisfiesRec (VarAssign VA v z) f DB)
  -- | VA, .All v f,   DB => (∀z ∈ Dom DB, SatisfiesRec (VarAssign VA v z) f DB)

-- Check whether a Formula can be satisfied for specified DatabaseInstance
def Satisfies : Formula → DatabaseInstance → Prop :=
  SatisfiesRec (λ _ ↦ .none)

-- Get the variables defined in the outermost .Ex formulae
def getResultVariables : Formula → List Variable
  | .Ex v f => getResultVariables f ++ [v]
  | _       => []

def hasDoubleVariables : Formula → List Variable → Prop
  | .Ex v f,  vs => hasDoubleVariables f (v :: vs) ∨ v ∈ vs
  -- | .All v f, vs => hasDoubleVariables f (v :: vs) ∨ v ∈ vs
  | _,        _ => False

-- def Evaluate : Formula → DatabaseInstance → VariableProjection → RelationInstance
--   | φ, DB, VP => RelationInstance.mk
--       {a |                          -- Attributes for which
--         ∃ v ∈ getResultVariables φ, -- Exists a variable in the result variable space
--         VP v = a                    -- That maps to the attribute
--       }
--       {t |                            -- Tuples for which
--         ∃ va : VariableAssignment,    -- Exists a variable assignment
--           SatisfiesRec va φ DB ∧      -- The variable assignment satisifies the formula on this database
--           ∀ v ∈ getResultVariables φ, -- For all result variables
--           ∀ a : Attribute,            -- AND For each attribute
--             (va.Dom v ∧ VP v = a) →   -- If variable is in the variable assignment AND the variable is projected to the attribute
--               t a = va v ∧            -- Then the tuple maps the attribute to the variable assigned value
--             ¬(va.Dom v ∧ VP v = a) →  -- Else
--               t a = .none             -- The attribute should be none
--       }
--       (by
--         sorry
--       )

end evaluate


-- Examples using FOL queries
section examples

def RSchema : RelationSchema := {"name", "age"}

def R : RelationInstance where
  schema := RSchema
  tuples := {
    λ a => match a with
    | "name" => "Alice"
    | "age" => "3"
    | _ => .none,
    λ a => match a with
    | "name" => "Bob"
    | "age" => "4"
    | _ => .none,
    λ a => match a with
    | "name" => "Charlie"
    | "age" => "5"
    | _ => .none
  }
  validSchema := by rw [RSchema]; aesop

def db : DatabaseInstance where
  schema := fun x => match x with
    | "R" => RSchema
    | _ => ∅
  relations := fun x => match x with
    | "R" => R
    | _ => ∅r ∅
  validSchema := by aesop


-- Ideally, formula 'f' is created using the following syntax
-- ∃ x y, R(name : x, age : y) ∧ x = "Alice" ∧ y = "3"

def f : Formula := .Ex "x" (.Ex "y" (
  .And (
    .R
      "R"
      fun
        | "name" => Term.var "x"
        | "age" => Term.var "y"
        | _ => .none
  )
  (.And
    (.Op (.Eq
      (.var "x")
      (.const "Alice")
    ))
    (.Op (.Eq
      (.var "y")
      (.const "3")
    ))
  )
))


-- Verify whether the examples work
example : Satisfies f db := by
  simp_all only [Satisfies, f, Part.coe_some, db, RSchema, R, SatisfiesRec, Dom, satisfies_rel,
    satisfies_tpl, getTerm, VarAssign, satisfies_op]
  simp_all
  -- Prove active domain containment for "x"
  -- When no equality restriction is put on "x", we need to help out a little
  apply And.intro
  · use "R"
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, PFun.dom_mk, exists_eq_left]
    apply Or.inl
    -- apply Or.inr
    use "name";
    intro a; rfl
  -- Prove active domain containment for "y"
  · apply And.intro
    . use "R"
      simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, PFun.dom_mk, exists_eq_left]
      apply Or.inl
      -- apply Or.inr
      use "age";
      intro a; rfl
    -- Prove satisfaction
    · aesop

end examples
