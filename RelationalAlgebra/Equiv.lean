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
theorem tuple_valid_schema {a : Attribute} {inst : RelationInstance} {t : Tuple} (ha : a ∈ inst.schema) (ht : t ∈ inst.tuples) : PFun.Dom t a := by
  rw [← inst.validSchema t ht] at *
  rw [PFun.mem_dom] at ha
  exact Part.dom_iff_mem.mpr ha

@[simp]
theorem not_tuple_valid_schema {a : Attribute} {inst : RelationInstance} {t : Tuple} (ha : a ∉ inst.schema) (ht : t ∈ inst.tuples) : ¬PFun.Dom t a := by
  rw [← inst.validSchema t ht] at ha
  exact ha

-- @[simp]
-- noncomputable def schema_union_comm {s1 s2 : RelationSchema} : {a // a ∈ s1 ∪ s2} ≃ {a // a ∈ s2 ∪ s1} where
--   toFun a := ⟨a.val, Or.symm a.prop⟩
--   invFun a := ⟨a.val, Or.symm a.prop⟩
--   left_inv a := by simp
--   right_inv a := by ext; simp

-- @[simp]
-- noncomputable def schema_union_self {s1 : RelationSchema} : s1 ≃ {a // a ∈ s1 ∪ s1} where
--   toFun a := ⟨a.1, Or.inl a.2⟩
--   invFun a := ⟨a.1, Or.elim a.2 id id⟩
--   left_inv a := by simp only [Subtype.coe_eta]
--   right_inv a := by simp only [Subtype.coe_eta]

-- @[simp]
-- noncomputable def tuple_equiv {s1 s2 : RelationSchema} (relation_equiv : s1 ≃ s2) : Tuple s1 ≃ Tuple s2 where
--   toFun a := λ x => a (relation_equiv.symm x)
--   invFun a := λ x => a (relation_equiv x)
--   left_inv a := by simp only [Equiv.symm_apply_apply]
--   right_inv a := by simp only [Equiv.apply_symm_apply]

-- @[simp]
-- noncomputable def instance_equiv {s1 s2 : RelationSchema} (relation_equiv : s1 ≃ s2) : RelationInstance s1 ≃ RelationInstance s2 where
--   toFun a := a.image (tuple_equiv relation_equiv)
--   invFun a := a.image (tuple_equiv relation_equiv.symm)
--   left_inv a := by
--     ext x : 1
--     simp only [tuple_equiv, Equiv.coe_fn_mk, Equiv.symm_symm, Set.mem_image, exists_exists_and_eq_and, Equiv.symm_apply_apply, exists_eq_right]
--   right_inv a := by
--     ext x : 1
--     simp only [tuple_equiv, Equiv.coe_fn_mk, Equiv.symm_symm, Set.mem_image, exists_exists_and_eq_and, Equiv.apply_symm_apply, exists_eq_right]
