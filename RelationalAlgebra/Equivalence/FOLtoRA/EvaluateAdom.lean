import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.Equivalence.FOLtoRA.Adom

open RM FOL

namespace FOL

def Query.evaluateAdom [Nonempty μ] (dbi : DatabaseInstance String String μ) {q : Query dbi.schema} [folStruc dbi] :
  RelationInstance String μ := ⟨q.schema, (q.evaluateT dbi ∩ {t | t.ran ⊆ dbi.domain}), λ _ ht ↦ realize_query_dom dbi ht.1⟩
