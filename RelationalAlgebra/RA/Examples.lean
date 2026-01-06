import RelationalAlgebra.RA.Query
import RelationalAlgebra.Examples

-- Define basic helper tactics to simplify repeated example proofs
syntax "singleton_tuple_mem" : tactic

macro_rules
  | `(tactic| singleton_tuple_mem) => `(tactic|
    ext a b;
    split;
    all_goals (
      grind
    )
  )


open RM RA

/-- Example query with selection -/
@[simp]
def exQuerySelection : Query String String :=
  .s "employee_id" "department_id" (.R "employee_department")

theorem hQuerySelection : exQuerySelection.isWellTyped exDatabase.schema := by
  simp_all [Query.isWellTyped]

#simp [Query.evaluate, Query.schema] (exQuerySelection.schema exDatabase.schema)

example : ∃t, t ∈ (exQuerySelection.evaluate exDatabase hQuerySelection).tuples := by
  simp only [Query.evaluate, Query.evaluateT, selectionT, exDatabase, exQuerySelection]
  simp only [String.reduceEq, imp_self, Set.mem_setOf_eq]

  use λ a => match a with
    | "employee_id" => "2"
    | "department_id" => "2"
    | _ => .none

  simp
  apply Or.inr
  apply Or.inl

  singleton_tuple_mem


/-- Example query with projection -/
@[simp]
def exQueryProjection : Query String String :=
  .p {"employee_name"} (.R "employee")

theorem hQueryProjection : exQueryProjection.isWellTyped exDatabase.schema := by
  simp_all [Query.isWellTyped]

#simp [Query.evaluate, Query.schema] (exQueryProjection.schema exDatabase.schema)

example : ∃t, t ∈ (exQueryProjection.evaluate exDatabase hQueryProjection).tuples := by
  simp only [Query.evaluate, Query.evaluateT, projectionT, exDatabase, exQueryProjection]
  simp only [String.reduceEq, imp_self, Set.mem_setOf_eq]

  use λ a => match a with
    | "employee_name" => "Bob"
    | _ => .none

  simp
  apply Or.inr
  apply Or.inl

  intro; simp_all only [String.reduceEq, implies_true, and_self]


/-- Example query with join -/
@[simp]
def exQueryJoin : Query String String :=
  .j (.R "employee") (.R "employee_department")

theorem hQueryJoin : exQueryJoin.isWellTyped exDatabase.schema := by
  simp_all [Query.isWellTyped]

#simp [Query.evaluate, Query.schema] (exQueryJoin.schema exDatabase.schema)

example : ∃t, t ∈ (exQueryJoin.evaluate exDatabase hQueryJoin).tuples := by
  simp only [Query.evaluate, Query.evaluateT, joinT, exDatabase, exQueryJoin]
  simp only [String.reduceEq, imp_self, Set.mem_setOf_eq]

  use λ a => match a with
    | "employee_id" => "1"
    | "employee_name" => "Anna"
    | "department_id" => "3"
    | _ => .none

  -- Left side of the join
  use λ a => match a with
    | "employee_id" => "1"
    | "employee_name" => "Anna"
    | _ => .none
  apply And.intro
  . simp
    apply Or.inl

    singleton_tuple_mem

  -- Right side of the join
  use λ a => match a with
    | "employee_id" => "1"
    | "department_id" => "3"
    | _ => .none
  apply And.intro
  . simp
    apply Or.inl

    singleton_tuple_mem

  -- Neither side of the join
  simp

  intro
  split_ands
  all_goals (
    intros
    split
    all_goals simp at *
  )


/-- Example query with rename -/
@[simp]
def exQueryRename : Query String String :=
  .r (renameFunc "employee_id" "id") (.R "employee")

theorem hQueryRename : exQueryRename.isWellTyped exDatabase.schema := by
  simp_all [Query.isWellTyped, rename_func_bijective]

#simp [Query.evaluate, Query.schema] (exQueryRename.schema exDatabase.schema)

example : ∃t, t ∈ (exQueryRename.evaluate exDatabase hQueryRename).tuples := by
  simp only [Query.evaluate, Query.evaluateT, renameT, exDatabase, exQueryRename]
  simp only [String.reduceEq, imp_self, Set.mem_setOf_eq]

  use λ a => match a with
    | "id" => "1"
    | "employee_name" => "Anna"
    | _ => .none

  simp
  apply Or.inl

  unfold renameFunc
  singleton_tuple_mem

/-- Example query with union -/
@[simp]
def exQueryUnion : Query String String :=
  .u (.R "employee") (.R "employee")

theorem hQueryUnion : exQueryUnion.isWellTyped exDatabase.schema := by
  simp_all [Query.isWellTyped]

#simp [Query.evaluate, Query.schema] (exQueryUnion.schema exDatabase.schema)

example : ∃t, t ∈ (exQueryUnion.evaluate exDatabase hQueryUnion).tuples := by
  simp only [Query.evaluate, Query.evaluateT, unionT, exDatabase, exQueryUnion]
  simp only [String.reduceEq, imp_self]

  use λ a => match a with
    | "employee_id" => "1"
    | "employee_name" => "Anna"
    | _ => .none

  simp
  apply Or.inl

  singleton_tuple_mem

/-- Example query with difference -/
@[simp]
def exQueryDifference : Query String String :=
  .d (.R "employee") (.R "employee")

theorem hQueryDifference : exQueryUnion.isWellTyped exDatabase.schema := by
  simp_all [Query.isWellTyped]

#simp [Query.evaluate, Query.schema] (exQueryDifference.schema exDatabase.schema)

example : ¬∃t, t ∈ (exQueryDifference.evaluate exDatabase hQueryDifference).tuples := by
  simp only [Query.evaluate, Query.evaluateT, diffT, exDatabase, exQueryDifference]
  simp only [String.reduceEq, imp_self]

  simp
