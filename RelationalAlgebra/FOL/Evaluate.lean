import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.RelabelProperties
import RelationalAlgebra.FOL.Realize

open FOL FirstOrder Language RM Term

namespace FOL

def Query.evaluateT (dbi : DatabaseInstance) (q : Query dbi.schema) [folStruc dbi] : Set Tuple :=
  {t | q.RealizeMin dbi t}

@[simp]
theorem Query.evaluateT.def {dbi : DatabaseInstance} [struc : folStruc dbi] {folQ : Query dbi.schema} :
  t ∈ folQ.evaluateT dbi ↔ folQ.RealizeMin dbi t := by rfl

@[simp]
theorem realize_query_dom {t : Attribute →. Value} (dbi : DatabaseInstance) {q : Query dbi.schema} [folStruc dbi] (h_realize : t ∈ q.evaluateT dbi) :
  t.Dom = q.schema := by
    ext a
    simp_all [PFun.mem_dom, Finset.mem_coe, Query.evaluateT]

def Query.evaluate (dbi : DatabaseInstance) {q : Query dbi.schema} [folStruc dbi] :
  RelationInstance := ⟨q.schema, q.evaluateT dbi, λ _ ht ↦ realize_query_dom dbi ht⟩
