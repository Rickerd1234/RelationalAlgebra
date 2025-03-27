import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Equiv
import RelationalAlgebra.Util

open RM

-- Selection and Difference are 'trivial', hence they are not included yet


-- Union
section union

def union (inst inst' : RelationInstance) (h: inst.schema = inst'.schema): RelationInstance := ⟨
    inst.schema,
    inst.tuples ∪ inst'.tuples,
    λ v hv => Or.elim hv (λ hv_l => inst.validSchema v hv_l) (λ hv_r => Eq.trans (inst'.validSchema v hv_r) h.symm)
  ⟩

@[simp]
theorem union_empty (inst : RelationInstance) : union inst emptyInst rfl = inst :=
  by unfold union; simp_all only [emptyInst, Set.union_empty]

@[simp]
theorem union_comm (inst inst' : RelationInstance) (h : inst.schema = inst'.schema) : union inst inst' h = union inst' inst h.symm :=
  by unfold union; simp [Set.union_comm inst.tuples inst'.tuples, h]

@[simp]
theorem union_assoc (inst inst' inst'' : RelationInstance) (h : inst.schema = inst'.schema) (h' : inst'.schema = inst''.schema) :
  union (union inst inst' h) inst'' (h.trans h') = union inst (union inst' inst'' h') (by simp [union, h]) :=
    by unfold union; simp [Set.union_assoc inst.tuples inst'.tuples inst''.tuples]

end union


-- Rename
section rename

@[simp]
theorem rename_in_old_schema {t : Tuple} {a a' a'' : Attribute} (prop : a'' ∈ t.schema \ {a} ∪ {a'}) (cond : a'' ≠ a') : a'' ∈ t.schema
  := Or.elim prop (λ h => h.left) (λ h => False.elim (cond h))

def renameSchema (schema : RelationSchema) (a a' : Attribute) (_ : a ∈ schema) (_ : a' ∉ (schema \ {a})) : RelationSchema := schema \ {a} ∪ {a'}

@[simp]
theorem rename_schema_id (schema : RelationSchema) (a : Attribute) (h : a ∈ schema) (h' : a ∉ (schema \ {a})) :
  renameSchema schema a a h h' = schema := by
    ext x
    simp_all only [renameSchema, Set.mem_diff, true_and, not_not, Set.diff_union_self, Set.mem_union, or_iff_left_iff_imp]
    exact λ y => by subst y; exact h

variable [DecidableEq Attribute]

def renameTuple (t : Tuple) (a a' : Attribute) (h : a ∈ t.schema) (h' : a' ∉ (t.schema \ {a})) : Tuple :=
  ⟨
    renameSchema t.schema a a' h h',
    λ a'' => if h_cond : a'' = a'
      then (t.val ⟨a, h⟩)
      else (t.val ⟨a'', rename_in_old_schema a''.prop h_cond⟩)
  ⟩

def rename (inst : RelationInstance) (a a' : Attribute) (h : a ∈ inst.schema) (h' : a' ∉ (inst.schema \ {a})) : RelationInstance := ⟨
    renameSchema inst.schema a a' h h',
    {
      t' | ∃ t : inst.tuples,
        t' = renameTuple t a a' (by rw [inst.validSchema t.val t.property]; exact h) (by rw [inst.validSchema t.val t.property]; exact h')
    },
    by
      intro t a
      simp_all only [Set.mem_diff, not_and, not_not, Subtype.exists, Set.mem_setOf_eq]
      obtain ⟨w, w_1, h_1⟩ := a
      simp_all only [inst.validSchema, renameTuple, renameSchema]
  ⟩

@[simp]
theorem rename_tuple_id (t : Tuple) (a : Attribute) (h : a ∈ t.schema) (h' : a ∉ (t.schema \ {a})) :
  renameTuple t a a h h' = t :=
    by unfold renameTuple; simp_all only


@[simp]
theorem rename_inst_id (inst : RelationInstance) (a : Attribute) (h : a ∈ inst.schema) (h' : a ∉ (inst.schema \ {a})):
  rename inst a a h h' = inst := by
    unfold rename
    -- Schema equality proof for singleton union
    have h1 : inst.schema ∪ {a} = inst.schema :=
      Set.ext λ y => ⟨
        (λ hy =>
          hy.elim id
          (λ hr => by
            subst hr
            simp_all only [true_and, not_not, Set.mem_union, or_true]
          )
        ),
        (λ hy => Or.inl hy)
      ⟩

    have h2 : (rename inst a a h h').tuples = inst.tuples := sorry

    simp [h1, h2]

@[simp]
theorem rename_comp {a a' a'' : Attribute} (inst : RelationInstance) (h1 : a ∈ inst.schema) (h1' : a' ∉ (inst.schema \ {a}))
  (h2 : a' ∈ (rename inst a a' h1 h1').schema) (h2' : a'' ∉ (rename inst a a' h1 h1').schema \ {a'}) (h3 : a ∈ inst.schema) (h3' : a'' ∉ inst.schema \ {a}) :
    rename (rename inst a a' h1 h1') a' a'' h2 h2' = rename inst a a'' h3 h3' := by
      unfold rename
      simp_all
      apply And.intro
      · sorry
      · sorry
      aesop?

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
