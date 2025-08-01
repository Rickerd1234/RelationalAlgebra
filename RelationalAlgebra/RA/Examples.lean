import RelationalAlgebra.RA.Query

open RM RA

def tup1 : Tuple
  | 0 => .some 11
  | 1 => .some 12
  | _ => .none

def tup2 : Tuple
  | 0 => .some 21
  | 1 => .some 22
  | _ => .none

def tup3 : Tuple
  | 0 => .some 31
  | 1 => .some 31
  | _ => .none

def tupA : Tuple
  | 1 => .some 11
  | 2 => .some 12
  | _ => .none

def tupB : Tuple
  | 1 => .some 21
  | 2 => .some 22
  | _ => .none

def tupC : Tuple
  | 1 => .some 31
  | 2 => .some 32
  | _ => .none

def relS : RelationSchema := {0, 1}
def relS2 : RelationSchema := {1, 2}

def relI : RelationInstance := ⟨
  relS,
  {tup1, tup2, tup3},
  by
    simp [relS, tup1, tup2, tup3, PFun.Dom]
    aesop
⟩
def relI2 : RelationInstance := ⟨
  relS2,
  {tupA, tupB, tupC},
  by
    simp [relS2, tupA, tupB, tupC, PFun.Dom]
    aesop
⟩

def dbI : DatabaseInstance := ⟨
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

def j : Query :=
  .s 0 1 true (.j (.R "R1") (.R "R2"))

theorem hj : j.isWellTyped dbI.schema := by
  simp_all [j, Query.isWellTyped, Query.schema, dbI, relS, relS2]

#simp [Query.evaluate, Query.schema, j, dbI, relS, relS2] (j.schema dbI.schema)

example : ∃t, t ∈ (j.evaluate dbI hj).tuples := by
  simp [Query.evaluate, Query.evaluateT, selectionT, joinT, j, dbI]

  use λ a => match a with
    | 0 => .some 31
    | 1 => .some 31
    | 2 => .some 32
    | _ => .none

  apply And.intro
  . simp only [relI, relI2, Set.mem_insert_iff, Set.mem_singleton_iff]
    use tup3
    simp only [true_or, or_true, true_and]
    use tupC
    simp only [true_or, or_true, true_and]

    intro a
    simp only [tup3, tupC]

    repeat (split; all_goals simp_all)
  . simp
