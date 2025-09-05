import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Evaluate
import RelationalAlgebra.FOL.Properties

open RM


def projectAttribute (folQ : FOL.Query) (rs : RelationSchema) (a' : Attribute) : Attribute ⊕ Fin ((folQ.attributesInQuery \ rs).card) :=
   ((RelationSchema.index? (folQ.attributesInQuery \ rs) a').map (Sum.inr)).getD (Sum.inl a')

@[simp]
theorem projectAttribute_eq {folQ rs x y} : projectAttribute folQ rs x = Sum.inl y → x = y := by
    simp [projectAttribute]
    have ⟨z, hz⟩ : ∃z : Option (Attribute ⊕ Fin (Finset.card (FOL.BoundedQuery.attributesInQuery folQ \ rs))),
      z = (Option.map Sum.inr ((RelationSchema.index? (folQ.attributesInQuery \ rs)) x))
        := exists_apply_eq_apply (fun a ↦ a) (Option.map Sum.inr (RelationSchema.index? (FOL.BoundedQuery.attributesInQuery folQ \ rs) x))
    by_cases h : z.isSome
    . simp only [Option.isSome_iff_exists] at h
      intro a
      subst hz
      simp_all only [Option.map_eq_some', Sum.exists, reduceCtorEq, and_false, exists_false, exists_const,
        Sum.inr.injEq, exists_eq_right, false_or]
      obtain ⟨w, h⟩ := h
      simp_all only [Option.map_some', Option.getD_some, reduceCtorEq]
    . simp at h
      subst h
      rw [hz.symm]
      simp [Option.getD_none]

@[simp]
theorem projectAttribute_mem {folQ rs a'} (h : a' ∈ rs) : projectAttribute folQ rs a' = Sum.inl a' := by
    simp [projectAttribute]
    have z : (Option.map Sum.inr ((RelationSchema.index? (folQ.attributesInQuery \ rs)) a')) =
      (Option.none : Option (Attribute ⊕ Fin (Finset.card (folQ.attributesInQuery \ rs))))
        := by simp_all only [RelationSchema.index?_none, Finset.mem_sdiff, not_true_eq_false, and_false, not_false_eq_true, Option.map_eq_none']

    rw [z]
    simp

@[simp]
theorem projectAttribute_not_mem {folQ rs a'} (h : a' ∈ folQ.attributesInQuery) (h' : a' ∉ rs) :
  ∃x, projectAttribute folQ rs a' = Sum.inr x := by
    simp [projectAttribute]

    have ⟨x, z2⟩ : ∃x, (Option.map Sum.inr ((RelationSchema.index? (folQ.attributesInQuery \ rs)) a')) =
      (Option.some (Sum.inr x) : Option (Attribute ⊕ Fin (Finset.card (folQ.attributesInQuery \ rs))))
        := by
          simp_all
          apply RelationSchema.index?_isSome_eq_iff.mp
          simp_all only [RelationSchema.index?_isSome, Finset.mem_sdiff, not_false_eq_true, and_self]

    use x
    rw [z2]
    simp

def projectQuery (folQ : FOL.Query) (rs : RelationSchema) : FOL.Query :=
  (folQ.relabel (projectAttribute folQ rs)).exs

@[simp]
theorem projectQuery.def [FOL.folStruc] (folQ : FOL.Query) (rs : RelationSchema) (h : rs ⊆ folQ.attributesInQuery) : (projectQuery folQ rs).attributesInQuery = rs := by
  ext a
  apply Iff.intro
  · intro a_1
    simp [FOL.BoundedQuery.attributesInQuery, projectQuery] at a_1
    obtain ⟨w, h_1⟩ := a_1
    obtain ⟨left, right⟩ := h_1
    have z := projectAttribute_eq right
    subst z
    by_cases h : w ∈ rs
    . simp_all only [projectAttribute_mem]
    . have z := projectAttribute_not_mem left h
      simp_all only [reduceCtorEq, exists_false]
  · intro a_1
    simp_all [FOL.BoundedQuery.attributesInQuery, projectQuery]
    use a
    apply And.intro
    · exact h a_1
    · exact projectAttribute_mem a_1
