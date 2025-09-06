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
def BoundedQuery.RealizeTerms {n : ℕ} [folStruc] : BoundedQuery n → (Attribute →. Value) → (Fin n →. Value) → Prop
  | R dbs rn t, ov, iv => (∀i, Term.realizeSome (t i) ov iv) ∧ (R dbs rn t).toFormula.Realize ov iv
  | tEq q t₁ t₂, ov, iv => q.RealizeTerms ov iv ∧ Term.realizeSome t₁ ov iv ∧ Term.realizeSome t₂ ov iv ∧ (BoundedFormula.equal t₁ t₂).Realize ov iv
  | and q₁ q₂, ov, iv => q₁.RealizeTerms ov iv ∧ q₂.RealizeTerms ov iv
  | ex q, ov, iv => ∃a, q.RealizeTerms ov (Fin.snoc iv a)

@[simp]
theorem BoundedQuery.RealizeTerms.R_def [folStruc] {n : ℕ} (t) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (R dbs rn t).RealizeTerms ov iv ↔ (∀i, Term.realizeSome (t i) ov iv) ∧ (R dbs rn t).toFormula.Realize ov iv := by
    rfl

@[simp]
theorem BoundedQuery.RealizeTerms.tEq_def [folStruc] {n : ℕ} (q : BoundedQuery n) (t₁ t₂ : fol.Term (Attribute ⊕ Fin n)) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (tEq q t₁ t₂).RealizeTerms ov iv ↔ (q.RealizeTerms ov iv ∧ Term.realizeSome t₁ ov iv ∧ Term.realizeSome t₂ ov iv ∧ (BoundedFormula.equal t₁ t₂).Realize ov iv) := by
    rfl

@[simp]
theorem BoundedQuery.RealizeTerms.and_def [folStruc] {n : ℕ} (q₁ q₂ : BoundedQuery n) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (and q₁ q₂).RealizeTerms ov iv ↔ q₁.RealizeTerms ov iv ∧ q₂.RealizeTerms ov iv := by
    rfl

@[simp]
theorem BoundedQuery.RealizeTerms.ex_def [folStruc] {n : ℕ} (q : BoundedQuery (n + 1)) {ov : Attribute →. Value} {iv : Fin n →. Value}
  : (ex q).RealizeTerms ov iv ↔ ∃a, q.RealizeTerms ov (Fin.snoc iv a) := by
    rfl

theorem Term.cases [folStruc] (t : fol.Term (Attribute ⊕ (Fin n))) : ∃k, t = var k := by
  cases t with | var k => use k | func _f _ => exact False.elim (folStruc_empty_fun _f)

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
  | q, ov, iv     => q.RealizeTerms ov iv ∧ q.RealizeValidDom dbi ov iv

@[simp]
theorem BoundedQuery.RealizeDom.def [folStruc] {q : BoundedQuery n} :
  q.RealizeDom dbi ov iv ↔ q.RealizeTerms ov iv ∧ q.RealizeValidDom dbi ov iv := by rfl

-- Realize a query considering the database domain, using just an Attribute
nonrec def Query.RealizeDom (φ : Query) (dbi : DatabaseInstance) [folStruc] (v : Attribute →. Value) : Prop :=
  φ.RealizeDom dbi v default ∧ v.Dom = φ.attributesInQuery

@[simp]
theorem Query.RealizeDom.def [folStruc] (φ : Query)
  : φ.RealizeDom dbi ov ↔ BoundedQuery.RealizeDom dbi φ ov default ∧ ov.Dom = φ.attributesInQuery := by rfl

@[simp]
theorem Query.RealizeDom.isWellTyped_def {iv : Fin n →. Value} [folStruc] (φ : BoundedQuery n) (h : φ.isWellTyped) (h' : φ.RealizeTerms t iv) :
 a ∈ BoundedQuery.attributesInQuery φ → (t a).Dom := by
    induction φ with
    | R =>
      aesop
      have z := Term.cases (a_1 w)
      aesop
      have z' := left w
      aesop
    | tEq sq t₁ t₂ sq_ih =>
      simp_all
      intro a_1
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right_1⟩ := h'
      simp_all only [BoundedQuery.isWellTyped.schema_eq_attributesInQuery]
      aesop
    | and => aesop
    | ex q q_ih => aesop

@[simp]
theorem Query.RealizeDom.isWellTyped_eq_Realize [folStruc] (φ : Query) (h : t ∈ (dbi.relations rn).tuples) (h' : φ.isWellTyped) (h'' : t.Dom = ↑φ.schema) :
 φ.RealizeDom dbi t = φ.RealizeTerms t default := by
    simp_all only [«def», BoundedQuery.RealizeDom.def, BoundedQuery.RealizeTerms,
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
      · simp_all only [(dbi.relations rn).validSchema, DatabaseInstance.validSchema_def,
        BoundedQuery.isWellTyped.schema_eq_attributesInQuery, Finset.coe_inj]
