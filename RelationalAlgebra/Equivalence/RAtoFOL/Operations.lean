import RelationalAlgebra.RA.Query
import RelationalAlgebra.FOL.Evaluate

open RM

section R

def att_to_var : Attribute → FOL.Variable :=
  Nat.repr

def var_to_att : FOL.Variable → Attribute :=
  String.toNat!

-- @TODO: Implement this, potentially using different definitions for the mapping in the first place
theorem var_to_att_to_var_eq_id {a} : var_to_att (att_to_var a) = a := by
  sorry

def schema_to_inFn {n} (dbs : DatabaseSchema) (rn : RelationName) : Attribute →. FOL.Language.fol.Term (FOL.Variable ⊕ Fin n) :=
  PFun.res (FOL.outVar ∘ att_to_var) (dbs rn)

-- def ra_to_fol_R {dbi} (rn : RelationName) : FOL.EvaluableQuery dbi := ⟨
--   .R dbi rn (FOL.outVar ∘ att_to_var ∘ (dbi.schema rn).fromIndex),
--   PFun.res att_to_var (dbi.schema rn),
--   by
--     apply Fintype.ofFinset (dbi.schema rn);
--     simp_all [PFun.res]
--   ,
--   byP
--     ext v
--     simp_all only [PFun.ran, PFun.res, PFun.restrict, Part.restrict, att_to_var, PFun.coe_val,
--       Part.get_some, Part.mem_mk_iff, Finset.mem_coe, exists_prop, Set.mem_toFinset,
--       Set.mem_setOf_eq, FOL.BoundedQuery.variablesInQuery, FOL.BoundedQuery.toFormula,
--       FirstOrder.Language.Relations.boundedFormula, FOL.fol.Rel,
--       FirstOrder.Language.BoundedFormula.freeVarFinset, Function.comp_apply, FOL.outVar,
--       FirstOrder.Language.Term.varFinsetLeft, Finset.mem_biUnion, Finset.mem_univ,
--       Finset.mem_singleton, true_and]
--     apply Iff.intro
--     · intro a
--       obtain ⟨w, h⟩ := a
--       obtain ⟨left, right⟩ := h
--       subst right
--       use RM.RelationSchema.index left
--       simp_all only [RelationSchema.fromIndex_index_eq]
--     · intro a
--       obtain ⟨w, h⟩ := a
--       use var_to_att v
--       subst h
--       rw [← att_to_var, var_to_att_to_var_eq_id]
--       exact And.intro (RelationSchema.fromIndex_mem w) rfl
-- ⟩

end R

section s


end s

section p

def ra_to_fol_query_p (w : FOL.Query) (rs : RelationSchema) : FOL.Query := w

def ra_to_fol_outFn_p (wOut : Attribute →. FOL.Variable) (rs : RelationSchema)
  : Attribute → Part FOL.Variable := λ a => ite (a ∈ rs) (wOut a) (Part.none)

end p

section r

def ra_to_fol_query_r (w : FOL.Query) (f : Attribute → Attribute) : FOL.Query := w

noncomputable def ra_to_fol_outFn_r (wOut : Attribute → Part FOL.Variable) (f : Attribute → Attribute)
  : Attribute → Part FOL.Variable := wOut ∘ f.invFun

-- noncomputable def ra_to_fol_r {dbi} (w : FOL.EvaluableQuery dbi) (f : Attribute → Attribute) (h : f.Bijective) : FOL.EvaluableQuery dbi := ⟨
--   ra_to_fol_query_r w.query f,
--   ra_to_fol_outFn_r w.outFn f,
--   by
--     apply Fintype.ofFinset (w.outFn.Dom.toFinset.image f);
--     intro x
--     simp_all only [Finset.mem_image, Set.mem_toFinset, PFun.mem_dom, Function.comp_apply, ra_to_fol_outFn_r]
--     apply Iff.intro
--     · intro a
--       obtain ⟨w_1, h_1⟩ := a
--       obtain ⟨left, right⟩ := h_1
--       obtain ⟨w_2, h_1⟩ := left
--       subst right
--       simp_all only [inv_f_id_apply]
--       apply Exists.intro w_2 h_1
--     · intro a
--       obtain ⟨w_1, h_1⟩ := a
--       apply Exists.intro
--       · apply And.intro (Exists.intro w_1 h_1)
--         · simp_all only [f_inv_id]
--   ,
--   by
--     rw [ra_to_fol_query_r, ← w.varsInQuery]
--     simp_all [PFun.ran]
--     ext v
--     simp_all only [Set.mem_setOf_eq]
--     apply Iff.intro
--     . intro a
--       obtain ⟨w_1, h_1⟩ := a
--       exact Exists.intro (Function.invFun f w_1) h_1
--     . intro ⟨w_1, h_1⟩
--       use f w_1
--       simp_all only [ra_to_fol_outFn_r, Function.comp_apply, inv_f_id_apply]
-- ⟩

end r
