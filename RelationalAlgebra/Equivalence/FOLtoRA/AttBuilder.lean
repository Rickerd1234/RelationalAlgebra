import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Util.Equiv
import RelationalAlgebra.FOL.Ordering

open RM

structure AttBuilder (n : ℕ) where
    rs : RelationSchema
    frs : RelationSchema
    s : (rs ∪ frs).card = n
    f2a : Fin n → { a // a ∈ (rs ∪ frs) }
    a2f : {a // a ∈ (rs ∪ frs)} → Fin n
    excl : rs ∩ frs = ∅
    bij : f2a.Bijective
    inv : a2f ∘ f2a = id

@[simp]
def AttBuilder.cast (ab : AttBuilder n) (h : n = m) : AttBuilder m := by rw [← h]; exact ab

@[simp]
def AttBuilder.schema (ab : AttBuilder n) : RelationSchema := ab.rs ∪ ab.frs

theorem AttBuilder.inv' (ab : AttBuilder n) : ab.f2a ∘ ab.a2f = id := by
  have := ab.bij
  simp [Function.Bijective, Function.Injective, Function.Surjective] at this
  obtain ⟨left, right⟩ := this
  funext a
  have ⟨b, hb⟩ := right a (by simp_rw [← @Finset.mem_union, Finset.coe_mem])
  rw [Subtype.coe_eta] at hb
  rw [← hb]
  rw [Function.comp_apply, id_eq]
  apply congr_arg
  simp_rw [← Function.comp_apply, ab.inv, id_eq]

theorem AttBuilder.surj' (ab : AttBuilder n) : ab.a2f.Surjective := by
  intro b
  use ab.f2a b
  simp_rw [← Function.comp_apply, ab.inv, id_eq]

theorem AttBuilder.inj' (ab : AttBuilder n) : ab.a2f.Injective := by
  intro a₁ a₂ a
  rw [← id_def a₁, ← id_def a₂, ← ab.inv', Function.comp_apply, Function.comp_apply]
  exact congrArg ab.f2a a

theorem AttBuilder.bij' (ab : AttBuilder n) : ab.a2f.Bijective := by
  apply And.intro (inj' ab) (surj' ab)

theorem AttBuilder.invFun (ab : AttBuilder n) [Nonempty (Fin n)] : ab.f2a.invFun = ab.a2f := by
  funext a
  nth_rewrite 1 [← id_def a, ← ab.inv']
  rw [
    Function.comp_apply (x := a),
    inv_f_id_apply ab.bij,
  ]

theorem AttBuilder.invFun' (ab : AttBuilder n) [Nonempty { a // a ∈ ab.rs ∪ ab.frs }] : ab.a2f.invFun = ab.f2a := by
  funext a
  nth_rewrite 1 [← id_def a, ← ab.inv]
  rw [
    Function.comp_apply (x := a),
    inv_f_id_apply ab.bij',
  ]


def AttBuilder.fromExcl {rs frs : RelationSchema} (excl : rs ∩ frs = ∅) (h : (rs ∪ frs).card = n) : AttBuilder n := ⟨
  rs,
  frs,
  h,
  λ a => ⟨(rs ∪ frs).fromIndex (a.cast h.symm), RelationSchema.fromIndex_mem (a.cast h.symm)⟩,
  λ a => ((rs ∪ frs).index (Finset.coe_mem a)).cast h,
  excl,
  by
    simp [Function.Bijective, Function.Injective]
    apply And.intro
    . intro a a'
      simp [RelationSchema.fromIndex_inj]
    . intro a
      have : ↑a ∈ rs ∪ frs := by simp only [Finset.coe_mem]
      use ((rs ∪ frs).index this).cast h
      simp,
  by
    ext x : 2
    simp_all only [Function.comp_apply, RelationSchema.index_fromIndex_eq, Fin.cast_cast,
      Fin.cast_eq_self, id_eq]
⟩

theorem card_lift_eq (ab : AttBuilder (n + 1)) :
  Finset.card ((Finset.erase ab.rs ↑(ab.f2a 0)) ∪ (Finset.erase ab.frs ↑(ab.f2a 0))) = n := by
    rw [← @Finset.erase_union_distrib]
    simp_all [ab.s]

def AttBuilder.liftExcl (ab : AttBuilder (n + 1)) : ab.rs.erase (ab.f2a 0) ∩ ab.frs.erase (ab.f2a 0) = ∅ := by
  rw [Finset.erase_inter, Finset.inter_erase, ab.excl]
  simp only [Finset.notMem_empty, not_false_eq_true, Finset.erase_eq_of_notMem]

def AttBuilder.lift (ab : AttBuilder (n + 1)) : AttBuilder n := AttBuilder.fromExcl (AttBuilder.liftExcl ab) (card_lift_eq ab)
