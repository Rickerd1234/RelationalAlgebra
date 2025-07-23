import RelationalAlgebra.RA.RelationalAlgebra

open RM

inductive Query : Type
  | R: RelationName → Query
  | s: Attribute → (Attribute ⊕ Value) → Bool → Query → Query
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

def Query.isWellTyped (dbs : DatabaseSchema) (q : Query) : Prop :=
  match q with
  | .R _ => (True)
  | .s a b _ sq => sq.isWellTyped dbs ∧ a ∈ sq.schema dbs ∧ b.elim (. ∈ sq.schema dbs) (fun _ => True)
  | .p rs sq => sq.isWellTyped dbs ∧ rs ⊆ sq.schema dbs
  | .j sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs
  | .r f sq => sq.isWellTyped dbs ∧ f.Surjective
  -- | .u sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs
  -- | .d sq1 sq2 => sq1.isWellTyped dbs ∧ sq2.isWellTyped dbs ∧ sq1.schema dbs = sq2.schema dbs

def Query.evaluateT (dbi : DatabaseInstance) (q : Query) : Set Tuple :=
  match q with
  | .R rn => (dbi.relations rn).tuples
  | .s a b posEq sq => selectionT (sq.evaluateT dbi) a b posEq
  | .p rs sq => projectionT (sq.evaluateT dbi) rs
  | .j sq1 sq2 => joinT (sq1.evaluateT dbi) (sq2.evaluateT dbi)
  | .r f sq => renameT (sq.evaluateT dbi) f
  -- | .u sq1 sq2 => unionT (sq1.evaluateT dbi) (sq2.evaluateT dbi)
  -- | .d sq1 sq2 => diffT (sq1.evaluateT dbi) (sq2.evaluateT dbi)

def Query.evaluate (dbi : DatabaseInstance) (q : Query) (h : q.isWellTyped dbi.schema) : RelationInstance :=
  ⟨
    q.schema dbi.schema,
    q.evaluateT dbi,
    by
      induction q with
      | R rn =>
        intro t h_t
        simp_all only [isWellTyped, evaluateT, schema, DatabaseInstance.validSchema]
        exact (dbi.relations rn).validSchema t h_t
      | s a b i sq ih =>
        simp_all only [isWellTyped, evaluateT, selectionT, schema]
        simp_all only [forall_const, Part.coe_some, bind_pure_comp, ne_eq, Set.mem_setOf_eq,
          implies_true]
      | p rs sq ih =>
        intros
        simp_all [isWellTyped, evaluateT, projectionT, schema]
        apply projectionDom ⟨sq.schema dbi.schema, evaluateT dbi sq, fun t h => ih t h⟩ ?_ h.2
        . simp_all only [projectionT, Set.mem_setOf_eq]
      | j sq1 sq2 ih1 ih2 =>
        intros
        simp_all [isWellTyped, evaluateT, joinT]
        apply joinDom
          ⟨sq1.schema dbi.schema, evaluateT dbi sq1, fun t h => ih1 t h⟩
          ⟨sq2.schema dbi.schema, evaluateT dbi sq2, fun t h => ih2 t h⟩
        . simp_all [joinT]
      | r f sq ih =>
        intros
        simp_all [isWellTyped, evaluateT, renameT, schema]
        apply renameDom ⟨sq.schema dbi.schema, evaluateT dbi sq, fun t h => ih t h⟩ h.2
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
