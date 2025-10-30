import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.RelabelProperties
import RelationalAlgebra.FOL.Realize

open FOL FirstOrder Language RM Term

namespace FOL

variable {ρ α μ : Type} [Nonempty μ]

def Query.evaluateT (dbi : DatabaseInstance String String μ) (q : Query dbi.schema) [folStruc dbi] : Set (String →. μ) :=
  {t | q.RealizeMin dbi t}

@[simp]
theorem Query.evaluateT.def {dbi : DatabaseInstance String String μ} [struc : folStruc dbi] {folQ : Query dbi.schema} :
  t ∈ folQ.evaluateT dbi ↔ folQ.RealizeMin dbi t := by rfl

@[simp]
theorem realize_query_dom (dbi : DatabaseInstance String String μ) {q : Query dbi.schema} [folStruc dbi] (h_realize : t ∈ q.evaluateT dbi) :
  t.Dom = q.schema := h_realize.1

def Query.evaluate (dbi : DatabaseInstance String String μ) {q : Query dbi.schema} [folStruc dbi] :
  RelationInstance String μ := ⟨q.schema, q.evaluateT dbi, λ _ ht ↦ realize_query_dom dbi ht⟩
