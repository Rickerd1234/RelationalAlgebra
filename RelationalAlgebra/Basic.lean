import RelationalAlgebra.RelationalModel

open RM

theorem t_ex_v_if_mem_schema {dbi : DatabaseInstance String String μ} (h : t ∈ (dbi.relations rn).tuples) (ha : a ∈ dbi.schema rn) :
  ∃v, v ∈ t a := by
    simp [← PFun.mem_dom, (dbi.relations rn).validSchema _ h, DatabaseInstance.validSchema, ha]

theorem t_eq_none_if_notMem_schema {dbi : DatabaseInstance String String μ} (h : t ∈ (dbi.relations rn).tuples) (ha : a ∉ dbi.schema rn) :
  t a = Part.none := by
    simp [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, (dbi.relations rn).validSchema _ h, DatabaseInstance.validSchema, ha]

theorem schema_notMem_if_forall_not_v {dbi : DatabaseInstance String String μ} (h : t ∈ (dbi.relations rn).tuples) (h' : ∀ (x : μ), x ∉ t a) :
  a ∉ dbi.schema rn := by
    rw [← DatabaseInstance.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema _ h, PFun.mem_dom]
    exact not_exists.mpr h'

theorem schema_mem_if_exists_v {dbi : DatabaseInstance String String μ} (h : t ∈ (dbi.relations rn).tuples) (h' : v ∈ t a) :
  a ∈ dbi.schema rn := by
    rw [← DatabaseInstance.validSchema, ← Finset.mem_coe, ← (dbi.relations rn).validSchema _ h, PFun.mem_dom]
    use v
