import RelationalAlgebra.RA.RelationalAlgebra

open RM

namespace RA

inductive Query : Type
  | R: RelationName → Query
  | s: Attribute → Attribute → Bool → Query → Query
  | p: RelationSchema → Query → Query
  | j: Query → Query → Query
  | r: (Attribute → Attribute) → Query → Query
  -- | u: Query → Query → Query
  -- | d: Query → Query → Query

def Query.schema : (q : Query) → (dbs : DatabaseSchema) → RelationSchema
  | .R rn => λ dbs => dbs rn
  | .s _ _ _ sq => sq.schema
  | .p rs _ => λ _ => rs
  | .j sq1 sq2 => λ dbs => sq1.schema dbs ∪ sq2.schema dbs
  | .r f sq => λ dbs => renameSchema (sq.schema dbs) f
  -- | .u sq1 _ => sq1.schema
  -- | .d sq1 _ => sq1.schema

@[simp]
theorem Query.schema_R (rn : RelationName) {dbs : DatabaseSchema} :
  (R rn).schema dbs = dbs rn := rfl

@[simp]
theorem Query.schema_s {dbs : DatabaseSchema} :
  (s a b pos sq).schema dbs = sq.schema dbs := rfl

@[simp]
theorem Query.schema_p (rs : RelationSchema) {dbs : DatabaseSchema} :
  (p rs sq).schema dbs = rs := rfl

@[simp]
theorem Query.schema_j {dbs : DatabaseSchema} :
  (j sq₁ sq₂).schema dbs = sq₁.schema dbs ∪ sq₂.schema dbs := rfl

@[simp]
theorem Query.schema_r {dbs : DatabaseSchema} :
  (r f sq).schema dbs = (sq.schema dbs).image f := rfl

def Query.isWellTyped (dbs : DatabaseSchema) (q : Query) : Prop :=
  match q with
  | .R _ => (True)
  | .s a b _ sq => sq.isWellTyped dbs ∧ a ∈ sq.schema dbs ∧ b ∈ sq.schema dbs
  | .p rs sq => sq.isWellTyped dbs ∧ rs ⊆ sq.schema dbs
  | .j sq₁ sq₂ => sq₁.isWellTyped dbs ∧ sq₂.isWellTyped dbs
  | .r f sq => sq.isWellTyped dbs ∧ f.Bijective
  -- | .u sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs
  -- | .d sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs

@[simp]
theorem Query.isWellTyped.R_def (rn : RelationName) {dbs : DatabaseSchema} :
  (R rn).isWellTyped dbs := by simp [isWellTyped]

@[simp]
theorem Query.isWellTyped.s_def {dbs : DatabaseSchema} :
  (s a b pos sq).isWellTyped dbs ↔ sq.isWellTyped dbs ∧ a ∈ sq.schema dbs ∧ b ∈ sq.schema dbs := by rfl

@[simp]
theorem Query.isWellTyped.p_def (rs : RelationSchema) {dbs : DatabaseSchema} :
  (p rs sq).isWellTyped dbs ↔ sq.isWellTyped dbs ∧ rs ⊆ sq.schema dbs := by rfl

@[simp]
theorem Query.isWellTyped.j_def {dbs : DatabaseSchema} :
  (j sq₁ sq₂).isWellTyped dbs ↔ sq₁.isWellTyped dbs ∧ sq₂.isWellTyped dbs := by rfl

@[simp]
theorem Query.isWellTyped.r_def {dbs : DatabaseSchema} :
  (r f sq).isWellTyped dbs ↔ sq.isWellTyped dbs ∧ f.Bijective := by rfl

def Query.evaluateT (dbi : DatabaseInstance) (q : Query) : Set Tuple :=
  match q with
  | .R rn => (dbi.relations rn).tuples
  | .s a b posEq sq => selectionT (sq.evaluateT dbi) a b posEq
  | .p rs sq => projectionT (sq.evaluateT dbi) rs
  | .j sq₁ sq₂ => joinT (sq₁.evaluateT dbi) (sq₂.evaluateT dbi)
  | .r f sq => renameT (sq.evaluateT dbi) f
  -- | .u sq1 sq2 => unionT (sq1.evaluateT dbi) (sq2.evaluateT dbi)
  -- | .d sq1 sq2 => diffT (sq1.evaluateT dbi) (sq2.evaluateT dbi)

@[simp]
theorem Query.evaluateT.R_def (rn : RelationName) (dbi : DatabaseInstance) :
  (R rn).evaluateT dbi = (dbi.relations rn).tuples := rfl

@[simp]
theorem Query.evaluateT.s_def :
  (s a b pos sq).evaluateT dbi = selectionT (sq.evaluateT dbi) a b pos := rfl

@[simp]
theorem Query.evaluateT.p_def (rs : RelationSchema) :
  (p rs sq).evaluateT dbi = projectionT (sq.evaluateT dbi) rs := rfl

@[simp]
theorem Query.evaluateT.j_def :
  (j sq₁ sq₂).evaluateT dbi = joinT (sq₁.evaluateT dbi) (sq₂.evaluateT dbi) := rfl

@[simp]
theorem Query.evaluateT.r_def :
  (r f sq).evaluateT dbi = renameT (sq.evaluateT dbi) f := rfl

def Query.evaluate (dbi : DatabaseInstance) (q : Query) (h : q.isWellTyped dbi.schema) : RelationInstance :=
  ⟨
    q.schema dbi.schema,
    q.evaluateT dbi,
    by
      induction q with
      | R rn =>
        intro t h_t
        simp_all only [isWellTyped, evaluateT, schema, ← DatabaseInstance.validSchema]
        exact RelationInstance.validSchema.def h_t
      | s a b i sq ih =>
        simp_all only [isWellTyped, evaluateT, selectionT, schema]
        simp_all only [forall_const, Part.coe_some, bind_pure_comp, ne_eq, Set.mem_setOf_eq,
          implies_true]
      | p rs sq ih =>
        intros
        simp_all [isWellTyped, evaluateT, projectionT, schema]
        apply projectionDom ⟨sq.schema dbi.schema, evaluateT dbi sq, ih⟩ ?_ h.2
        . simp_all only [projectionT, Set.mem_setOf_eq]
      | j sq1 sq2 ih1 ih2 =>
        intros t h
        simp_all only [isWellTyped, joinT, forall_const, Finset.coe_union]
        apply joinDom
          ⟨sq1.schema dbi.schema, evaluateT dbi sq1, ih1⟩
          ⟨sq2.schema dbi.schema, evaluateT dbi sq2, ih2⟩
          h
      | r f sq ih =>
        intros
        simp_all [isWellTyped, evaluateT, renameT, schema]
        apply renameDom ⟨sq.schema dbi.schema, evaluateT dbi sq, ih⟩ h.2
        . simp_all only [renameT, exists_eq_right', Set.mem_setOf_eq]
      -- | u sq1 sq2 ih =>
      --   intro _ ht
      --   simp_all [isWellTyped, evaluateT, unionT, schema]
      --   cases ht
      --   all_goals simp_all only
      -- | d sq1 sq2 ih =>
      --   intro _ ht
      --   simp_all [isWellTyped, evaluateT, diffT, schema]
      --   cases ht
      --   all_goals simp_all only
  ⟩
