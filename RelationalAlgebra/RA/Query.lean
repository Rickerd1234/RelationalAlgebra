import RelationalAlgebra.RA.RelationalAlgebra

open RM

namespace RA

inductive Query : Type
  | R: RelationName → Query
  | s: Attribute → Attribute → Query → Query
  | p: RelationSchema → Query → Query
  | j: Query → Query → Query
  | r: (Attribute → Attribute) → Query → Query
  | u: Query → Query → Query
  | d: Query → Query → Query

def Query.empty (rn : RelationName) : RA.Query := .d (.R rn) (.R rn)


@[simp]
def Query.schema : (q : Query) → (dbs : DatabaseSchema) → RelationSchema
  | .R rn => λ dbs => dbs rn
  | .s _ _ sq => sq.schema
  | .p rs _ => λ _ => rs
  | .j sq1 sq2 => λ dbs => sq1.schema dbs ∪ sq2.schema dbs
  | .r f sq => λ dbs => renameSchema (sq.schema dbs) f
  | .u sq1 _ => sq1.schema
  | .d sq1 _ => sq1.schema

@[simp]
theorem Query.schema.empty_def :
  (Query.empty rn).schema dbi = dbi rn := by simp only [empty, schema]


@[simp]
def Query.isWellTyped (dbs : DatabaseSchema) (q : Query) : Prop :=
  match q with
  | .R _ => (True)
  | .s a b sq => sq.isWellTyped dbs ∧ a ∈ sq.schema dbs ∧ b ∈ sq.schema dbs
  | .p rs sq => sq.isWellTyped dbs ∧ rs ⊆ sq.schema dbs
  | .j sq₁ sq₂ => sq₁.isWellTyped dbs ∧ sq₂.isWellTyped dbs
  | .r f sq => sq.isWellTyped dbs ∧ f.Bijective
  | .u sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs
  | .d sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs

@[simp]
theorem Query.isWellTyped.empty_def :
  (Query.empty rn).isWellTyped dbs := by simp only [empty, isWellTyped, schema, and_self]

@[simp]
def Query.evaluateT (dbi : DatabaseInstance) (q : Query) : Set Tuple :=
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


theorem Query.evaluate.validSchema {dbi} (q : Query) (h : q.isWellTyped dbi.schema) : ∀t, t ∈ q.evaluateT dbi → PFun.Dom t = ↑(q.schema dbi.schema) := by
  induction q with
  | R rn =>
    intro t h_t
    simp_all only [isWellTyped, evaluateT, schema, ← DatabaseInstance.validSchema]
    exact (dbi.relations rn).validSchema t h_t
  | s a b sq ih =>
    simp_all only [isWellTyped, evaluateT, selectionT, schema]
    simp_all only [forall_const, Part.coe_some, bind_pure_comp, ne_eq, Set.mem_setOf_eq,
      implies_true]
  | p rs sq ih =>
    intro t h_t
    simp_all [isWellTyped, evaluateT, projectionT, schema]
    apply projectionDom ⟨sq.schema dbi.schema, evaluateT dbi sq, ih⟩ ?_ h.2
    . simp_all only [projectionT, Set.mem_setOf_eq]
  | j sq1 sq2 ih1 ih2 =>
    intro t h_t
    simp_all only [isWellTyped, joinT, forall_const, Finset.coe_union]
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

def Query.evaluate (dbi : DatabaseInstance) (q : Query) (h : q.isWellTyped dbi.schema) : RelationInstance :=
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
theorem Query.evaluateT.mem_restrict {dbi t} {q : Query} (z : ↑(q.schema dbi.schema) ⊆ t.Dom)
  (h : q.isWellTyped dbi.schema) (h' : t ∈ q.evaluateT dbi) :
    t.restrict z ∈ q.evaluateT dbi := by
      have z' := (q.evaluate dbi h).validSchema t h'; have z'' := PFun.restrict.def_eq z z'.symm; simp_all only
