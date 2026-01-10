import RelationalAlgebra.RelationalModel

open RM

/- Very basic theorems connecting schema's and partial function domains -/
theorem t_ex_v_if_mem_schema {dbi : DatabaseInstance ρ α μ} (h : t ∈ (dbi.relations rn).tuples) (ha : a ∈ dbi.schema rn) :
  ∃v, v ∈ t a := by
    simp [← PFun.mem_dom, (dbi.relations rn).validSchema _ h, DatabaseInstance.validSchema, ha]

theorem t_eq_none_if_notMem_schema {dbi : DatabaseInstance ρ α μ} (h : t ∈ (dbi.relations rn).tuples) (ha : a ∉ dbi.schema rn) :
  t a = Part.none := by
    simp [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, (dbi.relations rn).validSchema _ h, DatabaseInstance.validSchema, ha]

theorem schema_notMem_if_forall_not_v {dbi : DatabaseInstance ρ α μ} (h : t ∈ (dbi.relations rn).tuples) (h' : ∀ (x : μ), x ∉ t a) :
  a ∉ dbi.schema rn := by
    rw [← DatabaseInstance.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema _ h, PFun.mem_dom]
    exact not_exists.mpr h'

theorem schema_mem_if_exists_v {dbi : DatabaseInstance ρ α μ} (h : t ∈ (dbi.relations rn).tuples) (h' : v ∈ t a) :
  a ∈ dbi.schema rn := by
    rw [← DatabaseInstance.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema _ h, PFun.mem_dom]
    use v

-- `PFun.Dom t a` derived from `v ∈ t a`
@[simp]
theorem value_mem_tuple_attr(h : v ∈ t a) : PFun.Dom t a := by
  rw [PFun.dom_eq]
  exact Exists.intro v h

-- `PFun.Dom t a` derived from `a ∈ inst.schema ∧ t ∈ inst.tuples`
@[simp]
theorem tuple_valid_schema {inst : RelationInstance α μ} (ha : a ∈ inst.schema) (ht : t ∈ inst.tuples) : PFun.Dom t a := by
  rw [← inst.schema.mem_coe, ← inst.validSchema t ht] at *
  rw [PFun.mem_dom] at ha
  exact Part.dom_iff_mem.mpr ha

-- `¬PFun.Dom t a` derived from `a ∉ inst.schema ∧ t ∈ inst.tuples`
@[simp]
theorem not_tuple_valid_schema {inst : RelationInstance α μ} (ha : a ∉ inst.schema) (ht : t ∈ inst.tuples) : ¬PFun.Dom t a := by
  rw [← inst.schema.mem_coe, ← inst.validSchema t ht] at ha
  exact ha
