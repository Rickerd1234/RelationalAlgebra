import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Realize
import RelationalAlgebra.FOL.Properties
import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

def Query.evaluateT (q : FOL.Query) (dbi : DatabaseInstance) [folStruc dbi] : Set Tuple :=
  {t | q.RealizeDom dbi t}

@[simp]
theorem realize_query_dom {t : Attribute →. Value}  {q : Query} (dbi : DatabaseInstance) [folStruc dbi] (h_realize : t ∈ q.evaluateT dbi) :
  t.Dom = q.schema := by
    ext a
    simp_all [PFun.mem_dom, Finset.mem_coe, Query.evaluateT]
    obtain ⟨w, h⟩ := h_realize
    obtain ⟨w_1, h⟩ := w
    obtain ⟨left, right⟩ := h
    apply Iff.intro
    . intro a_1
      obtain ⟨w, h_1⟩ := a_1
      apply h
      exact (PFun.mem_dom t a).mpr (Exists.intro w h_1)
    . intro a_1
      exact Part.dom_iff_mem.mp (left a (h (left a a_1)))

def Query.evaluate {q : Query} (dbi : DatabaseInstance) [folStruc dbi] :
  RelationInstance := ⟨q.schema, q.evaluateT dbi, λ _ ht ↦ realize_query_dom dbi ht⟩
