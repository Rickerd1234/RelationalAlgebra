import RelationalAlgebra.RelationalModel
import Mathlib.Data.Finset.Basic

open RM

-- Define basic helper tactics to simplify repeated example proofs
syntax "singleton_relation" : tactic

macro_rules
  | `(tactic| singleton_relation) => `(tactic|
    simp;
    split_ands;
    all_goals (
      ext;
      simp;
      split;
      all_goals (simp; try grind)
    )
  )

/- Basic example relation instances -/
@[simp]
def exRelationEmployee : RelationInstance String String := ⟨
  {"employee_id", "employee_name"},
  {
    λ a => match a with
    | "employee_id" => .some "1"
    | "employee_name" => .some "Anna"
    | _ => .none,
    λ a => match a with
    | "employee_id" => .some "2"
    | "employee_name" => .some "Bob"
    | _ => .none,
    λ a => match a with
    | "employee_id" => .some "3"
    | "employee_name" => .some "Charlie"
    | _ => .none
  },
  by singleton_relation
⟩

@[simp]
def exRelationDepartment : RelationInstance String String := ⟨
  {"department_id", "department_name"},
  {
    λ a => match a with
    | "department_id" => .some "a"
    | "department_name" => .some "Accounting"
    | _ => .none,
    λ a => match a with
    | "department_id" => .some "b"
    | "department_name" => .some "Business"
    | _ => .none
  },
  by singleton_relation
⟩

@[simp]
def exRelationEmployeeDepartment : RelationInstance String String := ⟨
  {"department_id", "employee_id"},
  {
    λ a => match a with
    | "department_id" => .some "3"
    | "employee_id" => .some "1"
    | _ => .none,
    λ a => match a with
    | "department_id" => .some "2"
    | "employee_id" => .some "2"
    | _ => .none,
    λ a => match a with
    | "department_id" => .some "1"
    | "employee_id" => .some "3"
    | _ => .none
  },
  by singleton_relation
⟩

/- Basic example database instance -/
@[simp]
def exDatabase : DatabaseInstance String String String := ⟨
  λ a => match a with
  | "department" => {"department_id", "department_name"}
  | "employee" => {"employee_id", "employee_name"}
  | "employee_department" => {"department_id", "employee_id"}
  | _ => ∅,

  λ a => match a with
  | "department" => exRelationDepartment
  | "employee" => exRelationEmployee
  | "employee_department" => exRelationEmployeeDepartment
  | _ => ⟨∅, ∅, by simp⟩,

  by intro; simp; split; all_goals simp
⟩
