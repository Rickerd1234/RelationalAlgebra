import RelationalAlgebra.RA.Query

open RM RA

def tup1 : String →. ℕ
  | "0" => .some 11
  | "1" => .some 12
  | _ => .none

def tup2 : String →. ℕ
  | "0" => .some 21
  | "1" => .some 22
  | _ => .none

def tup3 : String →. ℕ
  | "0" => .some 31
  | "1" => .some 31
  | _ => .none

def tupA : String →. ℕ
  | "1" => .some 11
  | "2" => .some 12
  | _ => .none

def tupB : String →. ℕ
  | "1" => .some 21
  | "2" => .some 22
  | _ => .none

def tupC : String →. ℕ
  | "1" => .some 31
  | "2" => .some 32
  | _ => .none

def relS : Finset String := {"0", "1"}
def relS2 : Finset String := {"1", "2"}

def relI : RelationInstance String ℕ := ⟨
  relS,
  {tup1, tup2, tup3},
  by
    simp [relS, tup1, tup2, tup3, PFun.Dom]
    aesop
⟩
def relI2 : RelationInstance String ℕ := ⟨
  relS2,
  {tupA, tupB, tupC},
  by
    simp [relS2, tupA, tupB, tupC, PFun.Dom]
    aesop
⟩

def dbI : DatabaseInstance String String ℕ := ⟨
  λ x => match x with
  | "R1" => relS
  | "R2" => relS2
  | _ => ∅,
  λ x => match x with
  | "R1" => relI
  | "R2" => relI2
  | _ => ∅r ∅,
  by
    intro rel
    simp_all only [RelationInstance.empty]
    split
    all_goals try rfl; try simp_all only [imp_false]
⟩

def j : Query String String :=
  .s "0" "1" (.j (.R "R1") (.R "R2"))

theorem hj : j.isWellTyped dbI.schema := by
  simp_all [j, Query.isWellTyped, Query.schema, dbI, relS, relS2]

#simp [Query.evaluate, Query.schema, j, dbI, relS, relS2] (j.schema dbI.schema)

example : ∃t, t ∈ (j.evaluate dbI hj).tuples := by
  simp [Query.evaluate, Query.evaluateT, selectionT, joinT, j, dbI]

  use λ a => match a with
    | "0" => .some 31
    | "1" => .some 31
    | "2" => .some 32
    | _ => .none

  apply And.intro
  . simp only [relI, relI2, Set.mem_insert_iff, Set.mem_singleton_iff]
    use tup3
    simp only [or_true, true_and]
    use tupC
    simp only [or_true, true_and]

    intro a
    simp only [tup3, tupC]

    repeat (split; all_goals simp_all)
  . simp
