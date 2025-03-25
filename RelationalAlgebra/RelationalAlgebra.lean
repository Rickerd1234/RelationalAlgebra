import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Equiv

open RM

-- Selection and Difference are 'trivial', hence they are not included yet


-- Union
section union

def union {s : RelationSchema} (inst inst' : RelationInstance s) : RelationInstance s := inst ∪ inst'

@[simp]
theorem union_empty {s : RelationSchema} (inst : RelationInstance s) :
  union inst ∅ = inst := Set.union_empty inst

@[simp]
theorem union_comm {s : RelationSchema} (inst inst' : RelationInstance s) :
  union inst inst' = union inst' inst := by exact Set.union_comm inst inst'

@[simp]
theorem union_assoc {s : RelationSchema} (inst inst' inst'' : RelationInstance s) :
  union (union inst inst') inst'' = union inst (union inst' inst'') := by exact Set.union_assoc inst inst' inst''

end union


-- Rename
section rename

def rename {s s' : RelationSchema} (inst : RelationInstance s) (f : s → s') : RelationInstance s' := { t' | ∃ t ∈ inst, t' ∘ f = t }

@[simp]
theorem rename_id {s : RelationSchema} (inst : RelationInstance s):
  rename inst id = inst := by simp only [rename, Function.comp_id, exists_eq_right', Set.setOf_mem_eq]

@[simp]
theorem rename_comp {s s' s'' : RelationSchema} (inst : RelationInstance s) (f : s → s') (g : s' → s'') (h : s → s'') (c : g ∘ f = h) :
  rename (rename inst f) g = rename inst h := by simp only [rename, exists_eq_right', Set.mem_setOf_eq, Function.comp_assoc, c]

@[simp]
theorem rename_inv {s s' : RelationSchema} (inst : RelationInstance s) (f : s → s') (g : s' → s) (c : g ∘ f = id) :
  rename (rename inst f) g = inst := by simp only [rename_comp, c, rename_id]

end rename


-- Join
section join

def join {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) (inst2 : RelationInstance s2) :
  RelationInstance (s1 ∪ s2) :=
    { t | ∃ t1 ∈ inst1, ∃ t2 ∈ inst2,
      -- Attributes in both s1 and s2
      (∀ a : ↑(s1 ∩ s2), t1 ⟨a, Set.mem_of_mem_inter_left a.prop⟩ = t2 ⟨a, Set.mem_of_mem_inter_right a.prop⟩) ∧
      -- Attributes in s1
      (∀ a : s1, t ⟨a, Or.inl a.prop⟩  = t1 a) ∧
      -- Attributes in s2
      (∀ a : s2, t ⟨a, Or.inr a.prop⟩  = t2 a)
    }

theorem join_empty {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) :
  join inst1 (∅ : RelationInstance s2) = (∅ : RelationInstance (s1 ∪ s2)) := by
    simp only [join, Set.mem_empty_iff_false, false_and, exists_const, and_false, Set.setOf_false]

theorem empty_join {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) :
  join (∅ : RelationInstance s2) inst1 = (∅ : RelationInstance (s2 ∪ s1)) := by
    simp only [join, Set.mem_empty_iff_false, false_and, exists_const, and_false, Set.setOf_false]

theorem join_comm {s1 s2 : RelationSchema} (inst1 : RelationInstance s1) (inst2 : RelationInstance s2) :
  join inst1 inst2 = (instance_equiv schema_union_comm) (join inst2 inst1) :=
    Set.ext λ t => ⟨ -- Proof by extensionality using tuple t
      -- t ∈ join inst1 inst2 → t ∈ (instance_equiv schema_union_comm) (join inst2 inst1)
      (
        λ ⟨l, l_in_1, r, r_in_2, both, t_in_l, t_in_r⟩ =>
          ⟨
            tuple_equiv schema_union_comm t,
            ⟨r, r_in_2, l, l_in_1,
              by
                simp [join];
                intro a b
                simp_all only [Subtype.forall, Set.mem_inter_iff, and_self],
              t_in_r,
              t_in_l
            ⟩,
            rfl
          ⟩
      ),
      -- t ∈ (instance_equiv schema_union_comm) (join inst2 inst1) → t ∈ join inst1 inst2
      (by
        intro ⟨s, ⟨l, l_in_2, r, r_in_1, both, s_in_l, s_in_r⟩, s_t⟩
        simp [join] at *
        subst s_t
        exact ⟨r, r_in_1, l, l_in_2,
          by simp_all only [and_self, implies_true],
        ⟩
      )
    ⟩

theorem join_self {s1 : RelationSchema} (inst1 : RelationInstance s1) :
  join inst1 inst1 = (instance_equiv schema_union_self) inst1 :=
    Set.ext λ t => ⟨ -- Proof by extensionality using tuple t
      -- t ∈ join inst1 inst1 → t ∈ (instance_equiv schema_union_self) inst1
      (λ ⟨l, l_in_1, r, r_in_1, both, t_in_l, t_in_r⟩ =>
        ⟨tuple_equiv schema_union_self.symm t,
          ⟨
            by
              simp [tuple_equiv, schema_union_self]
              simp_all only [Subtype.coe_prop, Subtype.coe_eta],
            rfl
          ⟩
        ⟩
      ),
      -- t ∈ (instance_equiv schema_union_self) inst1 → t ∈ join inst1 inst
      (by
        intro ⟨w, w_in_1, w_t⟩
        simp only [join, Subtype.forall]
        subst w_t
        exact ⟨w, w_in_1, w, w_in_1, λ _ _ => rfl, λ _ _ => rfl, λ _ _ => rfl⟩
      )
    ⟩

end join


-- Projection
section projection

def projection {s1 : RelationSchema} (inst1 : RelationInstance s1) (s2 : RelationSchema) (h : s2 ⊆ s1) :
  RelationInstance s2 :=
    { t | ∃ t1 ∈ inst1,
      (∀ a : s2, t a = t1 ⟨a, Set.mem_of_mem_of_subset a.prop h⟩)
    }

theorem projection_id {s1 : RelationSchema} (inst1 : RelationInstance s1) : projection inst1 s1 (by simp) = inst1 :=
  Set.ext λ t => ⟨ -- Proof by extensionality using tuple t
    -- t ∈ projection inst1 s1 ⋯ → t ∈ inst1
    (by
      intro ⟨w, w_in_1, w_project⟩
      have y : t = w := by
        ext x_1 : 1
        simp_all only [Subtype.coe_eta]
      subst y
      exact w_in_1
    ),
    -- t ∈ inst1 → t ∈ projection inst1 s1 ⋯
    (λ a => ⟨t, a, λ a => by simp only [Subtype.coe_eta]⟩)
  ⟩

theorem projection_cascade {s1 s2 s3 : RelationSchema} (inst1 : RelationInstance s1) (h1 : s2 ⊆ s1) (h2 : s3 ⊆ s2) :
  projection (projection inst1 s2 h1) s3 h2 = projection inst1 s3 (subset_trans h2 h1) :=
    Set.ext λ t => ⟨ -- Proof by extensionality using tuple t
      (
        -- x ∈ projection (projection inst1 s2 h1) s3 h2 → x ∈ projection inst1 s3 ⋯
        λ ⟨_, ⟨⟨w, w_in_1, project_1⟩, project_2⟩⟩ =>
          ⟨w, w_in_1, λ _ => by simp only [project_2, project_1]⟩
      ),
        -- x ∈ projection inst1 s3 ⋯ → x ∈ projection (projection inst1 s2 h1) s3 h2
      (
        λ ⟨w, w_in_1, w_project⟩ =>
          ⟨
            λ a => w ⟨a, Set.mem_of_mem_of_subset a.prop h1⟩,
            ⟨w, w_in_1, λ _ => rfl⟩,
            λ _ => by simp only [w_project]
          ⟩
      )
    ⟩

end projection
