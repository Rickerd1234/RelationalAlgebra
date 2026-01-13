import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.Equivalence.FOLtoRA.Adom

open RM FOL

namespace FOL

/-- Query evaluation for `RelationInstance`, restricting tuples to the active domain of the database. -/
def Query.evaluateAdom [Inhabited μ] (dbi : DatabaseInstance ρ α μ) {q : Query dbi.schema} [LinearOrder α] [folStruc dbi] :
  RelationInstance α μ := ⟨q.schema, (q.evaluateT dbi ∩ {t | t.ran ⊆ dbi.domain}), λ _ ht ↦ realize_query_dom dbi ht.1⟩
