import RelationalAlgebra.RelationalModel

open RM

-- Allow for deconstructing RelationInstance equivalence into separate schema and tuple equivalence
@[simp]
protected theorem RelationInstance.eq.mp : ∀ {a b : RelationInstance α μ}, (a.schema = b.schema ∧ a.tuples = b.tuples) → a = b
  | ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨rfl, rfl⟩ => rfl

@[simp]
protected theorem RelationInstance.eq.mpr : ∀ {a b : RelationInstance α μ}, a = b → a.schema = b.schema ∧ a.tuples = b.tuples
  := λ a_b => ⟨congrArg RelationInstance.schema a_b, congrArg RelationInstance.tuples a_b⟩

theorem RelationInstance.eq : ∀ {a b : RelationInstance α μ}, (a.schema = b.schema ∧ a.tuples = b.tuples) ↔ a = b :=
  Iff.intro (RelationInstance.eq.mp) (RelationInstance.eq.mpr)

@[simp]
theorem RelationInstance.dom_eq_schema {r : RelationInstance α μ} {h : t ∈ r.tuples} : t.Dom = r.schema :=
  by rw [RelationInstance.validSchema r t h]
