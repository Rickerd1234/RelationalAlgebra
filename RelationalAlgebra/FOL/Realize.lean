import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.FOL.Query
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

def BoundedQuery.RealizeValidDom (q : BoundedQuery n) (dbi : DatabaseInstance) (ov : Tuple) (iv : Fin n →. Value) : Prop :=
  (∀a ∈ q.attributesInQuery, (ov a).Dom) ∧ (ov.ran ⊆ dbi.domain) ∧ (∀i : Fin n, (iv i).Dom) ∧ (iv.ran ⊆ dbi.domain)

@[simp]
theorem BoundedQuery.RealizeValidDom.def [folStruc] {n : ℕ} (q : BoundedQuery n) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : q.RealizeValidDom dbi ov iv ↔
      (∀a ∈ q.attributesInQuery, (ov a).Dom) ∧ (ov.ran ⊆ dbi.domain) ∧
        (∀i : Fin n, (iv i).Dom) ∧ (iv.ran ⊆ dbi.domain)
  := by
    rfl

-- Realize a bounded query using Attribute and Fin n maps
def BoundedQuery.Realize {n : ℕ} [folStruc] : BoundedQuery n → (Attribute →. Value) → (Fin n →. Value) → Prop
  | q, ov, iv => q.toFormula.Realize ov iv

@[simp]
theorem BoundedQuery.Realize.def [folStruc] {n : ℕ} (q : BoundedQuery n) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : q.Realize ov iv ↔ q.toFormula.Realize ov iv := by
    rfl

-- Realize a bounded query considering the database domain, using Attribute and Fin n maps
def BoundedQuery.RealizeDom {n : ℕ} (dbi : DatabaseInstance) [folStruc] : BoundedQuery n → (Attribute →. Value) → (Fin n →. Value) → Prop
  -- | ex q, ov, iv  => (∃a iv', iv' = (Fin.snoc iv a) ∧ q.Realize ov iv' ∧ ov.ran ⊆ dbi.domain ∧ (PFun.ran iv') ⊆ dbi.domain)
  | q, ov, iv     => q.Realize ov iv ∧ q.RealizeValidDom dbi ov iv

@[simp]
theorem BoundedQuery.RealizeDom.def [folStruc] {q : BoundedQuery n} :
  q.RealizeDom dbi ov iv ↔ q.Realize ov iv ∧ q.RealizeValidDom dbi ov iv := by rfl

-- Realize a query considering the database domain, using just an Attribute
nonrec def Query.RealizeDom (φ : Query) (dbi : DatabaseInstance) [folStruc] (v : Attribute → Part Value) : Prop :=
  φ.RealizeDom dbi v (λ _ => .none)

@[simp]
theorem Query.RealizeDom.def [folStruc] (φ : Query)
  : φ.RealizeDom dbi ov = BoundedQuery.RealizeDom dbi φ ov (λ _ => .none) := rfl

@[simp]
theorem Query.RealizeDom.isWellTyped_def {iv : Fin n →. Value} [folStruc] (φ : BoundedQuery n) (h : φ.isWellTyped) (h' : φ.Realize t iv) :
 (t a).Dom ↔ a ∈ BoundedQuery.attributesInQuery φ := by
    simp_all
    induction φ with
    | R =>
      aesop
      . --have ⟨dbi, h_dbi, ht⟩ := folStruc_apply_RelMap h'
        -- have z' := (dbi.relations rn).validSchema_def ht
        -- simp_all [dbi.validSchema]
        -- subst h_dbi
        -- have z'' : a ∈ (dbi.schema rn) ↔ a ∈ PFun.Dom (ArityToTuple fun i ↦ realize (Sum.elim t iv) (a_1 i)) := by simp_all
        -- have z''' : a ∈ PFun.Dom (ArityToTuple fun i ↦ realize (Sum.elim t iv) (a_1 i)) := by
        --   simp [Part.dom_iff_mem, ← Part.eq_some_iff]
        --   use (t a).get a_2
        --   simp_all
        --   unfold ArityToTuple at *
        --   by_cases hc : a ∈ dbs rn
        --   . have z := RelationSchema.index?_isSome.mpr hc
        --     simp [Option.isSome_iff_exists] at z
        --     obtain ⟨w, h_2⟩ := z
        --     simp_all only [Option.map_some', Option.getD_some]
        --     have z' := h w

        --   . have z := RelationSchema.index?_none.mpr hc
        --     rw [z]
        --     aesop
        -- simp_all
        sorry
      . sorry --@TODO: Achieve this, possibly by changing the folStruc/isWellTyped concept
    | tEq sq t₁ t₂ sq_ih =>
      simp_all
      simp_all [sq_ih h'.1]
      intro a_1
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right_1⟩ := h'
      simp_all only [BoundedQuery.isWellTyped.schema_eq_attributesInQuery]
      cases a_1 with
      | inl h =>
        apply right
        simp_all only [Finset.mem_union, true_or]
      | inr h_1 =>
        apply right
        simp_all only [Finset.mem_union, or_true]
    | _ => aesop

@[simp]
theorem Query.RealizeDom.isWellTyped_eq_Realize [folStruc] (φ : Query) (h : t ∈ (dbi.relations rn).tuples) (h' : φ.isWellTyped) :
 φ.RealizeDom dbi t = φ.Realize t (λ _ => .none) := by
    simp_all
    intros h''
    apply And.intro
    . intros a h
      exact (isWellTyped_def φ h' h'').mpr h
    . apply And.intro
      . exact DatabaseInstance.t_ran_sub_domain h
      . simp_all [PFun.ran]
