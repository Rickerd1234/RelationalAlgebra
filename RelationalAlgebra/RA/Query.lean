import RelationalAlgebra.RA.RelationalAlgebra

open RM

namespace RA

inductive Query (ρ α : Type) : Type
  | R: ρ → Query ρ α
  | s: α → α → Query ρ α → Query ρ α
  | p: Finset α → Query ρ α → Query ρ α
  | j: Query ρ α → Query ρ α → Query ρ α
  | r: (α → α) → Query ρ α → Query ρ α
  | u: Query ρ α → Query ρ α → Query ρ α
  | d: Query ρ α → Query ρ α → Query ρ α

def Query.empty (rn : ρ) : RA.Query ρ α := .d (.R rn) (.R rn)


@[simp]
def Query.schema [DecidableEq α] : (q : Query ρ α) → (dbs : ρ → Finset α) → Finset α
  | .R rn => λ dbs => dbs rn
  | .s _ _ sq => sq.schema
  | .p rs _ => λ _ => rs
  | .j sq1 sq2 => λ dbs => sq1.schema dbs ∪ sq2.schema dbs
  | .r f sq => λ dbs => renameSchema (sq.schema dbs) f
  | .u sq1 _ => sq1.schema
  | .d sq1 _ => sq1.schema

@[simp]
theorem Query.schema.empty_def [DecidableEq α] :
  (Query.empty rn : Query ρ α).schema dbi = dbi rn := by simp only [empty, schema]


@[simp]
def Query.isWellTyped [DecidableEq α] (dbs : ρ → Finset α) (q : Query ρ α) : Prop :=
  match q with
  | .R _ => (True)
  | .s a b sq => sq.isWellTyped dbs ∧ a ∈ sq.schema dbs ∧ b ∈ sq.schema dbs
  | .p rs sq => sq.isWellTyped dbs ∧ rs ⊆ sq.schema dbs
  | .j sq₁ sq₂ => sq₁.isWellTyped dbs ∧ sq₂.isWellTyped dbs
  | .r f sq => sq.isWellTyped dbs ∧ f.Bijective
  | .u sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs
  | .d sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs

@[simp]
theorem Query.isWellTyped.empty_def [DecidableEq α] :
  (Query.empty rn : Query ρ α).isWellTyped dbs := by simp only [empty, isWellTyped, schema, and_self]

@[simp]
def Query.evaluateT (dbi : DatabaseInstance ρ α μ) (q : Query ρ α) : Set (α →. μ) :=
  match q with
  | .R rn => (dbi.relations rn).tuples
  | .s a b sq => selectionT (sq.evaluateT dbi) a b
  | .p rs sq => projectionT (sq.evaluateT dbi) rs
  | .j sq₁ sq₂ => joinT (sq₁.evaluateT dbi) (sq₂.evaluateT dbi)
  | .r f sq => renameT (sq.evaluateT dbi) f
  | .u sq1 sq2 => unionT (sq1.evaluateT dbi) (sq2.evaluateT dbi)
  | .d sq1 sq2 => diffT (sq1.evaluateT dbi) (sq2.evaluateT dbi)

@[simp]
theorem Query.evaluateT.empty_def :
  (Query.empty rn).evaluateT dbi = {} := by simp [empty, diffT, Set.diff]


theorem Query.evaluate.validSchema [DecidableEq α] (q : Query ρ α) (h : q.isWellTyped dbi.schema) : ∀t, t ∈ q.evaluateT dbi → PFun.Dom t = ↑(q.schema dbi.schema) := by
  induction q with
  | R rn =>
    intro t h_t
    simp_all only [isWellTyped, evaluateT, schema, ← DatabaseInstance.validSchema]
    exact (dbi.relations rn).validSchema t h_t
  | s a b sq ih =>
    simp_all only [isWellTyped, evaluateT, selectionT, schema]
    simp_all only [forall_const, Set.mem_setOf_eq, implies_true]
  | p rs sq ih =>
    intro t h_t
    simp_all [isWellTyped, evaluateT, projectionT, schema]
    apply projectionDom ⟨sq.schema dbi.schema, evaluateT dbi sq, ih⟩ ?_ h.2
    . simp_all only [projectionT, Set.mem_setOf_eq]
  | j sq1 sq2 ih1 ih2 =>
    intro t h_t
    simp_all only [isWellTyped, forall_const]
    apply joinDom
      ⟨sq1.schema dbi.schema, evaluateT dbi sq1, ih1⟩
      ⟨sq2.schema dbi.schema, evaluateT dbi sq2, ih2⟩
      h_t
  | r f sq ih =>
    intro t h_t
    apply renameDom ⟨sq.schema dbi.schema, evaluateT dbi sq, (by simp_all)⟩ h.2
    simp_all only [evaluateT, renameT, exists_eq_right', Set.mem_setOf_eq]
  | u sq1 sq2 ih =>
    intro _ ht
    simp_all [isWellTyped, evaluateT, unionT, schema]
    cases ht
    all_goals simp_all only
  | d sq1 sq2 ih =>
    intro _ ht
    simp_all [isWellTyped, evaluateT, diffT, schema]
    cases ht
    all_goals simp_all only

def Query.evaluate [DecidableEq α] (dbi : DatabaseInstance ρ α μ) (q : Query ρ α) (h : q.isWellTyped dbi.schema) : RelationInstance α μ :=
  ⟨
    q.schema dbi.schema,
    q.evaluateT dbi,
    by exact fun t a ↦ evaluate.validSchema q h t a
  ⟩


@[simp]
theorem PFun.restrict.def_eq {α β} {t : α →. β} {s : Set α} (h : s ⊆ t.Dom) (h' : s = t.Dom) :
  t.restrict h = t := by
    ext a b; aesop

@[simp]
theorem Query.evaluateT.mem_restrict [DecidableEq α] {q : Query ρ α} (z : ↑(q.schema dbi.schema) ⊆ t.Dom)
  (h : q.isWellTyped dbi.schema) (h' : t ∈ q.evaluateT dbi) :
    t.restrict z ∈ q.evaluateT dbi := by
      have z' := (q.evaluate dbi h).validSchema t h'; have z'' := PFun.restrict.def_eq z z'.symm; simp_all only
