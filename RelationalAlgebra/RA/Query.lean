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

def Query.schema : (q : Query) → (dbs : DatabaseSchema) → RelationSchema
  | .R rn => λ dbs => dbs rn
  | .s _ _ sq => sq.schema
  | .p rs _ => λ _ => rs
  | .j sq1 sq2 => λ dbs => sq1.schema dbs ∪ sq2.schema dbs
  | .r f sq => λ dbs => renameSchema (sq.schema dbs) f
  | .u sq1 _ => sq1.schema
  | .d sq1 _ => sq1.schema

@[simp]
theorem Query.schema_R (rn : RelationName) {dbs : DatabaseSchema} :
  (R rn).schema dbs = dbs rn := rfl

@[simp]
theorem Query.schema_s {dbs : DatabaseSchema} :
  (s a b sq).schema dbs = sq.schema dbs := rfl

@[simp]
theorem Query.schema_p (rs : RelationSchema) {dbs : DatabaseSchema} :
  (p rs sq).schema dbs = rs := rfl

@[simp]
theorem Query.schema_j {dbs : DatabaseSchema} :
  (j sq₁ sq₂).schema dbs = sq₁.schema dbs ∪ sq₂.schema dbs := rfl

@[simp]
theorem Query.schema_r {dbs : DatabaseSchema} :
  (r f sq).schema dbs = (sq.schema dbs).image f := rfl

@[simp]
theorem Query.schema_u {dbs : DatabaseSchema} :
  (u sq₁ sq₂).schema dbs = sq₁.schema dbs := by rfl

@[simp]
theorem Query.schema_d {dbs : DatabaseSchema} :
  (d q nq).schema dbs = q.schema dbs := by rfl

def Query.empty (rn : RelationName) : RA.Query := .d (.R rn) (.R rn)

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
theorem Query.isWellTyped.R_def (rn : RelationName) {dbs : DatabaseSchema} :
  (R rn).isWellTyped dbs := by simp [isWellTyped]

@[simp]
theorem Query.isWellTyped.s_def {dbs : DatabaseSchema} :
  (s a b sq).isWellTyped dbs ↔ sq.isWellTyped dbs ∧ a ∈ sq.schema dbs ∧ b ∈ sq.schema dbs := by rfl

@[simp]
theorem Query.isWellTyped.p_def (rs : RelationSchema) {dbs : DatabaseSchema} :
  (p rs sq).isWellTyped dbs ↔ sq.isWellTyped dbs ∧ rs ⊆ sq.schema dbs := by rfl

@[simp]
theorem Query.isWellTyped.j_def {dbs : DatabaseSchema} :
  (j sq₁ sq₂).isWellTyped dbs ↔ sq₁.isWellTyped dbs ∧ sq₂.isWellTyped dbs := by rfl

@[simp]
theorem Query.isWellTyped.r_def {dbs : DatabaseSchema} :
  (r f sq).isWellTyped dbs ↔ sq.isWellTyped dbs ∧ f.Bijective := by rfl

@[simp]
theorem Query.isWellTyped.u_def {dbs : DatabaseSchema} :
  (u sq1 sq2).isWellTyped dbs ↔ sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs := by rfl

@[simp]
theorem Query.isWellTyped.d_def {dbs : DatabaseSchema} :
  (d sq1 sq2).isWellTyped dbs ↔ sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs := by rfl

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
theorem Query.evaluateT.R_def (rn : RelationName) (dbi : DatabaseInstance) :
  (R rn).evaluateT dbi = (dbi.relations rn).tuples := rfl

@[simp]
theorem Query.evaluateT.s_def :
  (s a b sq).evaluateT dbi = selectionT (sq.evaluateT dbi) a b := rfl

@[simp]
theorem Query.evaluateT.p_def (rs : RelationSchema) :
  (p rs sq).evaluateT dbi = projectionT (sq.evaluateT dbi) rs := rfl

@[simp]
theorem Query.evaluateT.j_def :
  (j sq₁ sq₂).evaluateT dbi = joinT (sq₁.evaluateT dbi) (sq₂.evaluateT dbi) := rfl

@[simp]
theorem Query.evaluateT.r_def :
  (r f sq).evaluateT dbi = renameT (sq.evaluateT dbi) f := rfl

@[simp]
theorem Query.evaluateT.u_def :
  (u sq₁ sq₂).evaluateT dbi = unionT (sq₁.evaluateT dbi) (sq₂.evaluateT dbi) := rfl

@[simp]
theorem Query.evaluateT.d_def :
  (d sq nsq).evaluateT dbi = diffT (sq.evaluateT dbi) (nsq.evaluateT dbi) := rfl

theorem Query.evaluate.validSchema {dbi} (q : Query) (h : q.isWellTyped dbi.schema) : ∀t, t ∈ q.evaluateT dbi → PFun.Dom t = ↑(q.schema dbi.schema) := by
  induction q with
  | R rn =>
    intro t h_t
    simp_all only [isWellTyped, evaluateT, schema, ← DatabaseInstance.validSchema]
    exact RelationInstance.validSchema.def h_t
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
    simp_all [isWellTyped, evaluateT, renameT, schema]
    apply renameDom ⟨sq.schema dbi.schema, evaluateT dbi sq, ih⟩ h.2
    . simp_all only [renameT, exists_eq_right', Set.mem_setOf_eq]
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
theorem PFun.restrict.def_eq {α β} {t : α →. β} {s : Set α} (h : s ⊆ t.Dom) (h' : s = t.Dom) : t.restrict h = t := by ext a b; aesop

@[simp]
theorem Query.evaluateT.mem_restrict {dbi t} {q : Query} (z : ↑(q.schema dbi.schema) ⊆ t.Dom) (h : q.isWellTyped dbi.schema) (h' : t ∈ q.evaluateT dbi) :
  t.restrict z ∈ q.evaluateT dbi := by have z' := (q.evaluate dbi h).validSchema t h'; have z'' := PFun.restrict.def_eq z z'.symm; simp_all only

@[simp]
theorem Query.evaluateT.dbi_domain {dbi} {q : Query} (h : q.isWellTyped dbi.schema) : ∀t, t ∈ q.evaluateT dbi → t.ran ⊆ dbi.domain
  := by
    induction q with
    | R => exact fun t a ↦ DatabaseInstance.t_ran_sub_domain a

    | s a b sq => simp_all only [isWellTyped.s_def, s_def, selectionT, ne_eq, ite_true,
      Set.mem_setOf_eq, implies_true]

    | p rs sq ih =>
      simp_all [projectionT]
      intro t' t ht ha
      have z' : PFun.ran t' ⊆ PFun.ran t := by
        simp only [PFun.ran, Set.setOf_subset_setOf, forall_exists_index]
        intro v a h_dom
        by_cases hc : a ∈ rs
        . simp_all only; exact Exists.intro a h_dom
        . simp_all only [not_false_eq_true, Part.not_mem_none]
      exact Set.Subset.trans z' (ih t ht)

    | j q₁ q₂ ih₁ ih₂ =>
      simp_all only [isWellTyped.j_def, j_def, joinT, PFun.mem_dom, forall_exists_index,
        Set.mem_union, not_or, not_exists, and_imp, Set.mem_setOf_eq, forall_const]
      intro t' t₁ ht₁ t₂ ht₂ ht'

      have z' : PFun.ran t' ⊆ (PFun.ran t₁) ∪ (PFun.ran t₂) := by
        simp only [PFun.ran, Set.setOf_subset_setOf, Set.union_def]
        intro v ⟨a, ha⟩
        by_cases hc₁ : a ∈ t₁.Dom
        . simp_all; have ⟨y, hy⟩ := hc₁; rw [(ht' a).1 y hy] at ha; apply Or.inl (Exists.intro a ha)
        . by_cases hc₂ : a ∈ t₂.Dom
          . simp_all; have ⟨y, hy⟩ := hc₂; rw [(ht' a).2.1 y hy] at ha; apply Or.inr (Exists.intro a ha)
          . simp_all only [PFun.mem_dom, not_exists, Set.mem_setOf_eq, not_false_eq_true, implies_true,
              Part.not_mem_none]

      have : t₁.ran ∪ t₂.ran ⊆ dbi.domain := by simp_all only [Set.union_subset_iff, and_self]
      exact fun ⦃a⦄ a_1 ↦ this (z' a_1)

    | r f sq ih =>
      simp_all only [isWellTyped.r_def, r_def, renameT, exists_eq_right', Set.mem_setOf_eq,
        forall_const]
      intro t ht

      have z := ih (t ∘ f) ht
      have z' : (PFun.ran t) ⊆ PFun.ran (t ∘ f) := by
        simp [PFun.ran]
        intro v a ha
        use (f.invFun a)
        simp_all only [f_inv_id]

      exact fun ⦃a⦄ a_1 ↦ z (z' a_1)

    | u q₁ q₂ ih₁ ih₂ =>
      simp_all only [isWellTyped.u_def, u_def, unionT, Set.mem_union, forall_const]
      intro t ht
      cases ht with
      | inl ht₁ => exact ih₁ t ht₁
      | inr ht₂ => exact ih₂ t ht₂

    | d q nq ih nih =>
      simp_all only [isWellTyped.d_def, d_def, diffT, Set.diff, Set.mem_setOf_eq, implies_true]
