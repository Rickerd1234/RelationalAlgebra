import RelationalAlgebra.RelationalModel

open RM

@[simp]
protected theorem RelationInstance.eq.mp : ∀ {a b : RelationInstance}, (a.schema = b.schema ∧ a.tuples = b.tuples) → a = b
  | ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨rfl, rfl⟩ => rfl

@[simp]
protected theorem RelationInstance.eq.mpr : ∀ {a b : RelationInstance}, a = b → a.schema = b.schema ∧ a.tuples = b.tuples
  := λ a_b => ⟨congrArg RelationInstance.schema a_b, congrArg RelationInstance.tuples a_b⟩

theorem RelationInstance.eq : ∀ {a b : RelationInstance}, (a.schema = b.schema ∧ a.tuples = b.tuples) ↔ a = b :=
  Iff.intro (RelationInstance.eq.mp) (RelationInstance.eq.mpr)

@[simp]
theorem value_mem_tuple_attr {a : Attribute} {t : Tuple} {v : Value} (h : v ∈ t a) : PFun.Dom t a := by
  rw [PFun.dom_eq]
  rw [@Set.setOf_app_iff]
  exact Exists.intro v h

@[simp]
theorem tuple_valid_schema {a : Attribute} {inst : RelationInstance} {t : Tuple} (ha : a ∈ inst.schema) (ht : t ∈ inst.tuples) : PFun.Dom t a := by
  rw [← inst.validSchema t ht] at *
  rw [PFun.mem_dom] at ha
  exact Part.dom_iff_mem.mpr ha

@[simp]
theorem not_tuple_valid_schema {a : Attribute} {inst : RelationInstance} {t : Tuple} (ha : a ∉ inst.schema) (ht : t ∈ inst.tuples) : ¬PFun.Dom t a := by
  rw [← inst.validSchema t ht] at ha
  exact ha
