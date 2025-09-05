import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.Realize
import RelationalAlgebra.FOL.Properties
import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

def Query.evaluateT [folStruc] {q : FOL.Query} (dbi : DatabaseInstance) : Set Tuple :=
  {t | q.RealizeDom dbi t}

@[simp]
theorem realize_query_dom {t : Attribute →. Value} [folStruc] {q : Query} (dbi : DatabaseInstance) (h_wt : q.isWellTyped) (h_realize : q.RealizeDom dbi t) :
  t.Dom = q.schema := by
    ext a
    simp only [PFun.Dom, Query.RealizeDom.isWellTyped_def q h_wt (by simp_all; exact h_realize.1),
      Finset.setOf_mem, Finset.mem_coe, BoundedQuery.isWellTyped.schema_eq_attributesInQuery h_wt]

def Query.evaluate [folStruc] {q : Query} (h : q.isWellTyped) (dbi : DatabaseInstance)
  : RelationInstance := ⟨q.schema, q.evaluateT dbi, λ _ ht ↦ realize_query_dom dbi h ht⟩
