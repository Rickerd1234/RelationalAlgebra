import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Realize
import RelationalAlgebra.FOL.Properties
import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

def Query.evaluateT [folStruc] (q : FOL.Query) (dbi : DatabaseInstance) : Set Tuple :=
  {t | ∃ov : Tuple, ∃(h' : ↑q.schema ⊆ ov.Dom), q.RealizeDom dbi (ov.restrict h') ∧ t = (ov.restrict h')}

@[simp]
theorem realize_query_dom {t : Attribute →. Value} [folStruc] {q : Query} (dbi : DatabaseInstance) (h_wt : q.isWellTyped) (h_realize : t ∈ q.evaluateT dbi) :
  t.Dom = q.schema := by
    ext a
    simp_all [PFun.mem_dom, BoundedQuery.isWellTyped.schema_eq_attributesInQuery, Finset.mem_coe, Query.evaluateT]
    obtain ⟨w, h⟩ := h_realize
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := h
    subst right
    simp_all only [PFun.mem_restrict, BoundedQuery.isWellTyped.schema_eq_attributesInQuery, Finset.mem_coe,
      exists_and_left, and_iff_left_iff_imp]
    intro a_1
    exact Part.dom_iff_mem.mp (w_1 a_1)

def Query.evaluate [folStruc] {q : Query} (h : q.isWellTyped) (dbi : DatabaseInstance)
  : RelationInstance := ⟨q.schema, q.evaluateT dbi, λ _ ht ↦ realize_query_dom dbi h ht⟩
