import RelationalAlgebra.RelationalModel

theorem not_mem_singleton_iff {a b : α} : a ∉ ({b} : Set α) ↔ a ≠ b := Iff.rfl

-- Union
def union {relSch : RelationSchema} (relI relI' : RelationInstance relSch) : RelationInstance relSch := Set.union relI relI'

theorem union_comm {relSch : RelationSchema} (relI relI' : RelationInstance relSch) : union relI relI' = union relI' relI := by exact Set.union_comm relI relI'

-- Rename
def RenameSchema [DecidableEq Attribute] (relSch : RelationSchema) (oldA newA : Attribute) : RelationSchema := relSch \ {oldA} ∪ {newA}

def renameTuple {relSch : RelationSchema}
  [DecidableEq Attribute]
  (a a' : Attribute)
  (h : a ∈ relSch ∧ a' ∉ relSch)
  (t : Tuple relSch) : Tuple (RenameSchema relSch a a') := {
    val := λ att => t.val (if att = a' then a else att),
    inSchema := by
      -- Break open assumptions and simplify goal
      intro att att_in_rs'
      have ⟨v, old_inSchema⟩ := t
      rw [old_inSchema]

      -- Split if then else goal
      split_ifs with att_is_new
      . exact h.left
      . rw [RenameSchema] at att_in_rs'
        -- Case distinction on data
        cases att_in_rs' with
        | inl att_in_rs => exact Set.mem_of_mem_diff att_in_rs
        | inr att_in_new => exact False.elim (att_is_new att_in_new)
  }

def rename
  [DecidableEq Attribute]
  {relSch : RelationSchema}
  (relI : RelationInstance relSch)
  (a a' : Attribute)
  (h : a ∈ relSch ∧ a' ∉ relSch) : RelationInstance (RenameSchema relSch a a') := relI.image (renameTuple a a' h)

theorem rename_schema_id [DecidableEq Attribute] (relSch : RelationSchema) (a a' : Attribute) (h : a ∈ relSch ∧ a' ∉ relSch) : RenameSchema (RenameSchema relSch a a') a' a = relSch := by
  -- Rename schema simplification
  rw [RenameSchema, RenameSchema, Set.union_diff_right, Set.diff_diff_comm, Set.diff_union_self]
  -- Split hypothesis
  have ⟨hl, hr⟩ := h
  --
  apply Set.ext_iff.mpr
  intro x
  constructor
  -- x ∈ LHS → x ∈ RHS
  . intro h1
    simp at h1
    cases h1 with
    | inl h1 => exact h1.left
    | inr h1 => exact Set.mem_of_eq_of_mem h1 hl
  -- x ∈ RHS → x ∈ LHS
  . intro h1
    simp
    left
    constructor
    . exact h1
    . rw [not_mem_singleton_iff]
      by_contra xa'
      rw [xa'] at h1
      exact hr h1

theorem rename_id [DecidableEq Attribute] {relSch : RelationSchema} (relI : RelationInstance relSch)
  (a a' : Attribute) (h : a ∈ relSch ∧ a' ∉ relSch) (h2 : a' ∈ RenameSchema relSch a a' ∧ a ∉ RenameSchema relSch a a') :
  rename (rename relI a a' h) a' a h2 = relI := sorry
