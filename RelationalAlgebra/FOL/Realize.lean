import RelationalAlgebra.FOL.Ordering
import RelationalAlgebra.FOL.Query
import RelationalAlgebra.FOL.Schema
import RelationalAlgebra.FOL.WellTyped

open FOL FirstOrder Language RM Term

namespace FOL

def Term.realizeSome [folStruc] {n : ℕ} (t : fol.Term (Attribute ⊕ (Fin n))) (ov : Attribute →. Value) (iv : Fin n →. Value) : Prop
  := (t.realize (Sum.elim ov iv)).Dom

@[simp]
theorem Term.realizeSome.def [folStruc] (t : fol.Term (Attribute ⊕ (Fin n))) (ov : Attribute →. Value) (iv : Fin n →. Value) :
  Term.realizeSome t ov iv ↔ (t.realize (Sum.elim ov iv)).Dom := by rfl

-- Formal realization definition, requires all terms to be 'some'
def BoundedQuery.Realize {n : ℕ} [folStruc] : BoundedQuery n → (Attribute →. Value) → (Fin n →. Value) → Prop
  | R dbs rn t, ov, iv => (∀i, Term.realizeSome (t i) ov iv) ∧ (R dbs rn t).toFormula.Realize ov iv
  | tEq q t₁ t₂, ov, iv => q.Realize ov iv ∧ Term.realizeSome t₁ ov iv ∧ Term.realizeSome t₂ ov iv ∧ (BoundedFormula.equal t₁ t₂).Realize ov iv
  | and q₁ q₂, ov, iv => q₁.Realize ov iv ∧ q₂.Realize ov iv
  | ex q, ov, iv => ∃a, q.Realize ov (Fin.snoc iv a)

@[simp]
theorem BoundedQuery.Realize.R_def [folStruc] {n : ℕ} (t) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (R dbs rn t).Realize ov iv ↔ (∀i, Term.realizeSome (t i) ov iv) ∧ (R dbs rn t).toFormula.Realize ov iv := by
    rfl

@[simp]
theorem BoundedQuery.Realize.tEq_def [folStruc] {n : ℕ} (q : BoundedQuery n) (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (tEq q t₁ t₂).Realize ov iv ↔ (q.Realize ov iv ∧ Term.realizeSome t₁ ov iv ∧ Term.realizeSome t₂ ov iv ∧ (BoundedFormula.equal t₁ t₂).Realize ov iv) := by
    rfl

@[simp]
theorem BoundedQuery.Realize.and_def [folStruc] {n : ℕ} (q₁ q₂ : BoundedQuery n) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (and q₁ q₂).Realize ov iv ↔ q₁.Realize ov iv ∧ q₂.Realize ov iv := by
    rfl

@[simp]
theorem BoundedQuery.Realize.ex_def [folStruc] {n : ℕ} (q : BoundedQuery (n + 1)) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (ex q).Realize ov iv ↔ ∃a, q.Realize ov (Fin.snoc iv a) := by
    rfl

-- Realize a bounded query doamin, all values must be within dbi.domain and both assignments must have 'some' values for all used terms
def BoundedQuery.RealizeValidDom (q : BoundedQuery n) (dbi : DatabaseInstance) (ov : Tuple) (iv : Fin n →. Value) : Prop :=
  (∀a ∈ q.schema, (ov a).Dom) ∧ (ov.ran ⊆ dbi.domain) ∧ (∀i : Fin n, (iv i).Dom) ∧ (iv.ran ⊆ dbi.domain)

@[simp]
theorem BoundedQuery.RealizeValidDom.def [folStruc] {n : ℕ} (q : BoundedQuery n) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : q.RealizeValidDom dbi ov iv ↔
      (∀a ∈ q.schema, (ov a).Dom) ∧ (ov.ran ⊆ dbi.domain) ∧
        (∀i : Fin n, (iv i).Dom) ∧ (iv.ran ⊆ dbi.domain)
  := by
    rfl

-- Realize a bounded query considering the database domain, using Attribute and Fin n maps
def BoundedQuery.RealizeDom {n : ℕ} (dbi : DatabaseInstance) [folStruc] : BoundedQuery n → (Attribute →. Value) → (Fin n →. Value) → Prop
  | q, ov, iv     => q.Realize ov iv ∧ q.RealizeValidDom dbi ov iv

@[simp]
theorem BoundedQuery.RealizeDom.def [folStruc] {q : BoundedQuery n} :
  q.RealizeDom dbi ov iv ↔ q.Realize ov iv ∧ q.RealizeValidDom dbi ov iv := by rfl

-- Realize a query considering the database domain, using just an Attribute map
nonrec def Query.RealizeDom (φ : Query) (dbi : DatabaseInstance) [folStruc] (v : Attribute →. Value) : Prop :=
  φ.RealizeDom dbi v default ∧ v.Dom ⊆ φ.schema

@[simp]
theorem Query.RealizeDom.def [folStruc] (φ : Query)
  : φ.RealizeDom dbi ov ↔ BoundedQuery.RealizeDom dbi φ ov default ∧ ov.Dom ⊆ φ.schema := by rfl

theorem Query.RealizeDom.schema_sub_Dom [folStruc] (q : FOL.Query) (h : q.isWellTyped) (h': q.RealizeDom dbi ov) :
  ↑q.schema ⊆ ov.Dom := by simp_all; aesop

@[simp]
theorem Query.RealizeDom.isWellTyped_def {iv : Fin n →. Value} [folStruc]
  (φ : BoundedQuery n) (h : φ.isWellTyped) (h' : φ.Realize t iv) (ha : a ∈ BoundedQuery.schema φ):
    (t a).Dom := by
      induction φ with
      | R dbs rn f =>
        simp_all [BoundedQuery.isWellTyped.R_def, BoundedQuery.Realize.R_def, Term.realizeSome.def,
          BoundedQuery.toFormula_rel, BoundedFormula.realize_rel, folStruc_apply_RelMap,
          BoundedQuery.attributesInQuery.R_def, Set.mem_toFinset, Set.mem_setOf_eq]
        obtain ⟨left, right⟩ := h'
        obtain ⟨w, h⟩ := ha
        have z := Term.cases (f w)
        simp_all [Sum.exists]
        cases z with
        | inl h_1 =>
          obtain ⟨w_2, h_1⟩ := h_1
          simp_all only [varFinsetLeft.eq_1, Finset.mem_singleton]
          subst h
          have z' := left w
          simp_all only [realize_var, Sum.elim_inl]
        | inr h_2 =>
          obtain ⟨w_2, h_1⟩ := h_2
          simp_all only [varFinsetLeft.eq_2, Finset.not_mem_empty]
      | tEq sq t₁ t₂ sq_ih =>
        simp_all
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right_1⟩ := h'
        simp_all only [BoundedQuery.isWellTyped.schema_eq_attributesInQuery]
        aesop
      | and => aesop
      | ex q q_ih => aesop

@[simp]
theorem Query.RealizeDom.isWellTyped_eq_Realize [folStruc]
  (φ : Query) (h : t ∈ (dbi.relations rn).tuples)
  (h' : φ.isWellTyped) (h'' : t.Dom ⊆ ↑φ.schema) :
    φ.RealizeDom dbi t = φ.Realize t default := by
      simp_all only [«def», BoundedQuery.RealizeDom.def, BoundedQuery.Realize,
        BoundedQuery.RealizeValidDom.def, zero_le, Part.not_none_dom, IsEmpty.forall_iff, true_and,
        eq_iff_iff, and_iff_left_iff_imp, and_imp]
      apply Iff.intro
      · intro a
        simp_all only
      · intro h''
        simp_all only [true_and]
        apply And.intro
        · apply And.intro
          · intro a h
            exact isWellTyped_def φ h' h'' h
          · apply And.intro
            · exact DatabaseInstance.t_ran_sub_domain h
            · simp_all [PFun.ran]
        · simp_all [(dbi.relations rn).validSchema, DatabaseInstance.validSchema_def,
          BoundedQuery.isWellTyped.schema_eq_attributesInQuery, Finset.coe_inj]
