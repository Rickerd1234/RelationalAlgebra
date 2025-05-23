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

abbrev VariableAssignment := Variable → Value

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
def getTerm : VariableAssignment → Term → Value
  | _,  .const c => c
  | VA, .var v   => VA v

-- Verify whether a Formula.R is satisfied
def satisfies_rel : RelationName → AttributeAssignment → DatabaseInstance → VariableAssignment → Prop
  | RN, AA, DB, VA =>
      ∃ tpl ∈ (DB.relations RN).tuples, -- There exists a tuple in the relation
      ∀ att ∈ (DB.relations RN).schema, -- Where for all attributes in the schema
      ∃ trm : Term,                     -- There exists a term
        AA.Dom att →                    -- If attribute is assigned in the formula
          AA att = some trm ∧           -- Then this assigned term
          getTerm VA trm = tpl att      -- Should match the value for this attribute in the tuple

-- Verify whether a Formula.Op is satisfied
def satisfies_op : Atom →  DatabaseInstance → VariableAssignment → Prop
  | .Eq t1 t2, _, VA => getTerm VA t1 = getTerm VA t2

-- Check whether a VariableAssignment satisfies a Formula for specified DatabaseInstance
def Satisfies : Formula → DatabaseInstance → VariableAssignment → Prop
  | .R rn aa,   DB, VA => satisfies_rel rn aa DB VA
  | .Op a,      DB, VA => satisfies_op a DB VA
  | .And l r,   DB, VA => Satisfies l DB VA ∧ Satisfies r DB VA
  -- | .Or l r,    DB, VA => Satisfies l DB VA ∨ Satisfies r DB VA
  -- | .Not f,     DB, VA => ¬Satisfies f DB vA
  | .Ex v f,    DB, VA => (∃z ∈ Dom DB, VA v = z ∧ Satisfies f DB VA)
  -- | .All v f    DB, VA => (∀z ∈ Dom DB, VA v = z ∧ Satisfies f DB VA)

-- def Evaluate : Formula → DatabaseInstance → (Variable →. Attribute) → RelationInstance
--   | φ, DB, VA => RelationInstance.mk
--       {a |            -- Attributes for which
--         ∃ v ∈ VA.Dom, -- Exists a variable in the partial function domain
--         VA v = a      -- That maps to the attribute
--       }
--       {t |                          -- Tuples for which
--         ∃ s : VariableAssignment,   -- Exists a variable assignment
--           Satisfies φ DB s ∧        -- The variable assignment satisifies the formula on this database
--           ∀ a : Attribute,          -- AND For each attribute
--           ∃ v : Variable,           -- There exists a variable
--             (VA.Dom v ∧ VA v = a) → -- If the variable is mapped to the attribute
--               t a = s v ∧           -- Then the tuple maps the attribute to the variable assigned value
--             ¬(VA.Dom v ∧ VA v = a) →
--               t a = .none
--       }
--       (by
--         intro t a
--         simp_all only [Part.coe_some, and_self, not_true_eq_false, and_false, IsEmpty.forall_iff, implies_true,
--           exists_const, and_true, Set.mem_setOf_eq, PFun.mem_dom]
--         obtain ⟨w, h⟩ := a
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
    | "age" => "3"
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


def f : Formula := .Ex "x" (.Ex "y" (
  .And (
    .R
      "R"
      fun
        | "name" => Term.var "x"
        | "age" => Term.var "y"
        | _ => .none
  ) (.Op (.Eq
    (.var "y")
    (.const "3")
  ))
))

def va : VariableAssignment
  | "x" => "Alice"
  | "y" => "3"
  | _ => ""


-- Verify whether the examples work
example : Satisfies f db va := by
  simp_all only [Satisfies, f, db, va, R, RSchema, satisfies_rel, Dom, satisfies_op, Part.coe_some, getTerm]
  simp_all
  apply And.intro
  -- Prove active domain containment for "x"
  · use "R"
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, PFun.dom_mk, exists_eq_left]
    -- apply Or.inr
    apply Or.inl
    use "name";
    intro a; rfl
  -- Prove active domain containment for "y"
  · apply And.intro
    . use "R"
      simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, PFun.dom_mk, exists_eq_left]
      -- apply Or.inr
      apply Or.inl
      use "age";
      intro a; rfl
    · aesop

end examples
