import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Util.Equiv
import RelationalAlgebra.FOL.Ordering

open RM

structure AttBuilder (rs : RelationSchema) (n : ℕ) where
    frs : RelationSchema
    f2a : Fin n → { a // a ∈ rs ∪ frs }
    a2f : {a // a ∈ rs ∪ frs} → Fin n
    excl : rs ∩ frs = ∅
    bij : f2a.Bijective
    inv : a2f ∘ f2a = id

theorem AttBuilder.inv' (ab : AttBuilder rs n) : ab.f2a ∘ ab.a2f = id := by
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

theorem AttBuilder.surj' (ab : AttBuilder rs n) : ab.a2f.Surjective := by
  intro b
  use ab.f2a b
  simp_rw [← Function.comp_apply, ab.inv, id_eq]

theorem AttBuilder.inj' (ab : AttBuilder rs n) : ab.a2f.Injective := by
  intro a₁ a₂ a
  rw [← id_def a₁, ← id_def a₂, ← ab.inv', Function.comp_apply, Function.comp_apply]
  exact congrArg ab.f2a a

theorem AttBuilder.bij' (ab : AttBuilder rs n) : ab.a2f.Bijective := by
  apply And.intro (inj' ab) (surj' ab)

theorem AttBuilder.invFun (ab : AttBuilder rs n) [Nonempty (Fin n)] : ab.f2a.invFun = ab.a2f := by
  funext a
  nth_rewrite 1 [← id_def a, ← ab.inv']
  rw [
    Function.comp_apply (x := a),
    inv_f_id_apply ab.bij,
  ]

theorem AttBuilder.invFun' (ab : AttBuilder rs n) [Nonempty { a // a ∈ rs ∪ ab.frs }] : ab.a2f.invFun = ab.f2a := by
  funext a
  nth_rewrite 1 [← id_def a, ← ab.inv]
  rw [
    Function.comp_apply (x := a),
    inv_f_id_apply ab.bij',
  ]


def AttBuilder.fromExcl {rs frs : RelationSchema} (excl : rs ∩ frs = ∅) : AttBuilder rs (rs ∪ frs).card := ⟨
  frs,
  λ a => ⟨(rs ∪ frs).fromIndex a, RelationSchema.fromIndex_mem a⟩,
  λ a => (rs ∪ frs).index (Finset.coe_mem a),
  excl,
  by
    simp [Function.Bijective, Function.Injective]
    apply And.intro
    . intro a a'
      simp [RelationSchema.fromIndex_inj]
    . intro a
      have : ↑a ∈ rs ∪ frs := by simp only [Finset.coe_mem]
      use ((rs ∪ frs).index this)
      simp,
  by
    ext x : 2
    simp_all only [Function.comp_apply, RelationSchema.index_fromIndex_eq, id_eq]
⟩
