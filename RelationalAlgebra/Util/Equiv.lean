import RelationalAlgebra.RelationalModel

open RM

-- Useful helper theorems

-- Allow for deconstructing RelationInstance equivalence into separate schema and tuple equivalence
@[simp]
protected theorem RelationInstance.eq.mp : ∀ {a b : RelationInstance}, (a.schema = b.schema ∧ a.tuples = b.tuples) → a = b
  | ⟨_,_,_⟩, ⟨_,_,_⟩, ⟨rfl, rfl⟩ => rfl

@[simp]
protected theorem RelationInstance.eq.mpr : ∀ {a b : RelationInstance}, a = b → a.schema = b.schema ∧ a.tuples = b.tuples
  := λ a_b => ⟨congrArg RelationInstance.schema a_b, congrArg RelationInstance.tuples a_b⟩

theorem RelationInstance.eq : ∀ {a b : RelationInstance}, (a.schema = b.schema ∧ a.tuples = b.tuples) ↔ a = b :=
  Iff.intro (RelationInstance.eq.mp) (RelationInstance.eq.mpr)

@[simp]
theorem RelationInstance.dom_eq_schema {t : Tuple} {r : RelationInstance} {h : t ∈ r.tuples} : t.Dom = r.schema :=
  by rw [RelationInstance.validSchema r t h]

-- `PFun.Dom t a` derived from `v ∈ t a`
@[simp]
theorem value_mem_tuple_attr {a : Attribute} {t : Tuple} {v : Value} (h : v ∈ t a) : PFun.Dom t a := by
  rw [PFun.dom_eq]
  exact Exists.intro v h

-- `PFun.Dom t a` derived from `a ∈ inst.schema ∧ t ∈ inst.tuples`
@[simp]
theorem tuple_valid_schema {a : Attribute} {inst : RelationInstance} {t : Tuple} (ha : a ∈ inst.schema) (ht : t ∈ inst.tuples) : PFun.Dom t a := by
  rw [← inst.schema.mem_coe, ← inst.validSchema t ht] at *
  rw [PFun.mem_dom] at ha
  exact Part.dom_iff_mem.mpr ha

-- `¬PFun.Dom t a` derived from `a ∉ inst.schema ∧ t ∈ inst.tuples`
@[simp]
theorem not_tuple_valid_schema {a : Attribute} {inst : RelationInstance} {t : Tuple} (ha : a ∉ inst.schema) (ht : t ∈ inst.tuples) : ¬PFun.Dom t a := by
  rw [← inst.schema.mem_coe, ← inst.validSchema t ht] at ha
  exact ha

section invFun

variable {a : Attribute} {f : Attribute → Attribute}

@[simp]
theorem inv_f_id (h : f.Bijective) : (Function.invFun f ∘ f) a = a
  := by simp_all only [Function.invFun_comp h.1, id_eq]

@[simp]
theorem inv_f_id_apply (h : f.Bijective) : Function.invFun f (f a) = a
  := inv_f_id h

@[simp]
theorem f_inv_id (h : f.Bijective) : f (Function.invFun f a) = a
  := by simp_all only [Function.Bijective, Function.Surjective, Function.invFun_eq]
