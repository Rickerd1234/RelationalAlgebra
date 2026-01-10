import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.RelabelProperties
import RelationalAlgebra.FOL.Realize

open FOL FirstOrder Language RM Term

namespace FOL

variable {ρ α μ : Type} [Nonempty μ]

/-- Query evaluation for a `Set` of tuples, get all tuples satisfying the FOL query, restricted to the variables used in the formula -/
def Query.evaluateT (dbi : DatabaseInstance ρ String μ) (q : Query dbi.schema) [folStruc dbi] : Set (String →. μ) :=
  {t | q.RealizeMin dbi t}

@[simp]
theorem Query.evaluateT.def {dbi : DatabaseInstance ρ String μ} [struc : folStruc dbi] {folQ : Query dbi.schema} :
  t ∈ folQ.evaluateT dbi ↔ folQ.RealizeMin dbi t := by rfl

@[simp]
theorem realize_query_dom (dbi : DatabaseInstance ρ String μ) {q : Query dbi.schema} [folStruc dbi] (h_realize : t ∈ q.evaluateT dbi) :
  t.Dom = q.schema := h_realize.1

/--
Query evaluation for a `RelationInstance`, get the `RelationInstance` satisfying the FOL query,
with the schema restricted to the variables used in the formula
-/
def Query.evaluate (dbi : DatabaseInstance ρ String μ) {q : Query dbi.schema} [folStruc dbi] :
  RelationInstance String μ := ⟨q.schema, q.evaluateT dbi, λ _ ht ↦ realize_query_dom dbi ht⟩
