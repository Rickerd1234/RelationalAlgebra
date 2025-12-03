import RelationalAlgebra.RelationalModel

open RM

theorem t_eq_none_if_notMem_schema {dbi : DatabaseInstance String String μ} (h : t ∈ (dbi.relations rn).tuples) (ha : a ∉ dbi.schema rn) :
  t a = Part.none := by
    simp [Part.eq_none_iff', Part.dom_iff_mem, ← PFun.mem_dom, (dbi.relations rn).validSchema _ h, DatabaseInstance.validSchema, ha]
