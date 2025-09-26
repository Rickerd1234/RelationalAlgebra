import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Realize
import RelationalAlgebra.FOL.RelabelProperties
import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

def Query.evaluateT (q : FOL.Query) (dbi : DatabaseInstance) [folStruc dbi] : Set Tuple :=
  {t | q.RealizeDom dbi t}

@[simp]
theorem Query.evaluateT.def {dbi : DatabaseInstance} [struc : FOL.folStruc dbi] {folQ : FOL.Query} :
  t ∈ folQ.evaluateT dbi ↔ folQ.RealizeDom dbi t := by rfl

@[simp]
theorem realize_query_dom {t : Attribute →. Value}  {q : Query} (dbi : DatabaseInstance) [folStruc dbi] (h_realize : t ∈ q.evaluateT dbi) :
  t.Dom = q.schema := by
    ext a
    simp_all [PFun.mem_dom, Finset.mem_coe, Query.evaluateT]
    obtain ⟨h_realize, h_t_sub_schema⟩ := h_realize
    apply Iff.intro
    . intro a_1
      obtain ⟨w, h_1⟩ := a_1
      apply h_t_sub_schema
      exact (PFun.mem_dom t a).mpr (Exists.intro w h_1)
    . intro a_1
      have left := BoundedQuery.Realize.schema_sub_Dom h_realize
      exact Part.dom_iff_mem.mp (left a (h_t_sub_schema (left a a_1)))

def Query.evaluate {q : Query} (dbi : DatabaseInstance) [folStruc dbi] :
  RelationInstance := ⟨q.schema, q.evaluateT dbi, λ _ ht ↦ realize_query_dom dbi ht⟩
