import RelationalAlgebra.FOL.Query

open FOL FirstOrder Language RM Term

namespace FOL

-- Realize a bounded query using Attribute and Fin n maps
def BoundedQuery.Realize {n : ℕ} [folStruc] : BoundedQuery n → (Attribute →. Value) → (Fin n →. Value) → Prop
  | R dbs rn t, ov, iv => (R dbs rn t).toFormula.Realize ov iv ∧ ∀i : Fin (Finset.card (dbs rn)), ((t i).realize (Sum.elim ov iv)).Dom
  | tEq t₁ t₂, ov, iv => (tEq t₁ t₂).toFormula.Realize ov iv ∧ (t₁.realize (Sum.elim ov iv)).Dom ∧ (t₂.realize (Sum.elim ov iv)).Dom
  | q, ov, iv => q.toFormula.Realize ov iv

@[simp]
theorem query_realize_rel_def [folStruc] {n : ℕ} {dbs : DatabaseSchema} {rn : RelationName} {vMap : Fin (dbs rn).card → fol.Term (Attribute ⊕ Fin n)} {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (BoundedQuery.R dbs rn vMap).Realize ov iv ↔ (BoundedQuery.R dbs rn vMap).toFormula.Realize ov iv ∧ ∀i : Fin (Finset.card (dbs rn)), ((vMap i).realize (Sum.elim ov iv)).Dom := by
    rfl

@[simp]
theorem query_realize_tEq_def [folStruc] {n : ℕ} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (BoundedQuery.tEq t₁ t₂).Realize ov iv ↔ (BoundedQuery.tEq t₁ t₂).toFormula.Realize ov iv ∧ (t₁.realize (Sum.elim ov iv)).Dom ∧ (t₂.realize (Sum.elim ov iv)).Dom := by
    rfl

@[simp]
theorem query_realize_and_def [folStruc] {n : ℕ} {q₁ q₂ : BoundedQuery n} {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (BoundedQuery.and q₁ q₂).Realize ov iv ↔ (BoundedQuery.and q₁ q₂).toFormula.Realize ov iv := by
    rfl

@[simp]
theorem query_realize_ex_def [folStruc] {n : ℕ} {q : BoundedQuery (n + 1)} {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (BoundedQuery.ex q).Realize ov iv ↔ (BoundedQuery.ex q).toFormula.Realize ov iv := by
    rfl

-- Realize a bounded query considering the database domain, using Attribute and Fin n maps
def BoundedQuery.RealizeDom {n : ℕ} (dbi : DatabaseInstance) [folStruc] : BoundedQuery n → (Attribute →. Value) → (Fin n →. Value) → Prop
  | ex q, ov, iv  => (∃a ∈ dbi.domain, q.Realize ov (Fin.snoc iv a)) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain
  | q, ov, iv     => q.Realize ov iv ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain

-- Realize a query considering the database domain, using just an Attribute
nonrec def Query.Realize (φ : Query) (dbi : DatabaseInstance) [folStruc] (v : Attribute → Part Value) : Prop :=
  φ.RealizeDom dbi v (λ _ => .none)

@[simp]
theorem query_realize_rel [folStruc] {n : ℕ} {dbi : DatabaseInstance} {rn : RelationName} {vMap : Fin (dbi.schema rn).card → fol.Term (Attribute ⊕ Fin n)} {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (BoundedQuery.R dbi.schema rn vMap).RealizeDom dbi ov iv ↔ (BoundedQuery.R dbi.schema rn vMap).Realize ov iv ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain := by
    rfl

@[simp]
theorem query_realize_tEq [folStruc] {n : ℕ} {dbi : DatabaseInstance} {t₁ t₂ : fol.Term (Attribute ⊕ Fin n)} {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (BoundedQuery.tEq t₁ t₂).RealizeDom dbi ov iv ↔ (BoundedQuery.tEq t₁ t₂).Realize ov iv ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain := by
    rfl

@[simp]
theorem query_realize_and [folStruc] {n : ℕ} {dbi : DatabaseInstance} {q1 q2 : BoundedQuery n} {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (q1.and q2).RealizeDom dbi ov iv ↔ ((q1.and q2).Realize ov iv ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain) := by
    rfl

@[simp]
theorem query_realize_ex [folStruc] {n : ℕ} {dbi : DatabaseInstance} {q : BoundedQuery (n + 1)} {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (q.ex).RealizeDom dbi ov iv ↔ (∃ a ∈ dbi.domain, q.Realize ov (Fin.snoc iv a)) ∧ ov.ran ⊆ dbi.domain ∧ iv.ran ⊆ dbi.domain := by
    rfl
