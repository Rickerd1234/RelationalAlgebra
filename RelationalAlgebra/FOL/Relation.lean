-- import RelationalAlgebra.RelationalModel
-- import RelationalAlgebra.FOL.Variable

-- namespace FOL

-- open RM Language

-- structure RelationTermRestriction (n: ℕ) where
--   inFn : Attribute →. fol.Term (Variable ⊕ Fin n)
--   name : RelationName
--   fintypeDom : Fintype inFn.Dom

-- instance {n : ℕ} (rtr : RelationTermRestriction n) : Fintype rtr.inFn.Dom := rtr.fintypeDom

-- def RelationTermRestriction.schema {n: ℕ} (rtr : RelationTermRestriction n) : RelationSchema := rtr.inFn.Dom.toFinset

-- def RelationTermRestriction.vars {n : ℕ} (rtr : RelationTermRestriction n) : Finset (fol.Term (Variable ⊕ Fin n)) := rtr.inFn.ran.toFinset

-- def RelationTermRestriction.outVars {n : ℕ} (rtr : RelationTermRestriction n) : Finset Variable :=
--   rtr.vars.filterMap outVar? outVar?.injective

-- -- Bounded relation term restriction, used to bind a specific database instance and verify the schema
-- structure BoundedRelationTermRestriction (n : ℕ) extends RelationTermRestriction n where
--   dbi : DatabaseInstance
--   validSchema : inFn.Dom.toFinset = dbi.schema name

-- def liftTerm {n m : ℕ} (term : fol.Term (Variable ⊕ Fin n)) (h : n ≤ m) : fol.Term (Variable ⊕ Fin m) :=
--   term.relabel (Sum.map id fun i => Fin.castLE h i)

-- def liftInFn {n m : ℕ} (inFn : Attribute →. fol.Term (Variable ⊕ Fin n)) (h : n ≤ m) : Attribute →. fol.Term (Variable ⊕ Fin m) :=
--   λ att => (inFn att).map (λ term => liftTerm term h)

-- def BoundedRelationTermRestriction.lift {n m : ℕ} (brtr : BoundedRelationTermRestriction n) (h : n ≤ m) : BoundedRelationTermRestriction m :=
--   {brtr with inFn := liftInFn brtr.inFn h}


-- def BoundedRelationTermRestriction.relationInstance {n : ℕ} (brtr : BoundedRelationTermRestriction n) : RelationInstance := brtr.dbi.relations brtr.name

-- @[simp]
-- theorem brtr_schema_dbi_def {n : ℕ} (brtr : BoundedRelationTermRestriction n) : brtr.schema = brtr.dbi.schema brtr.name := by
--   simp only [RelationTermRestriction.schema, brtr.validSchema, Finset.toFinset_coe]

-- @[simp]
-- theorem att_in_dom {n att} {brtr : BoundedRelationTermRestriction n}
--   :  (∃ var, var ∈ brtr.inFn att) ↔ att ∈ brtr.dbi.schema brtr.name := by
--     simp_all only [← brtr.validSchema, Set.mem_toFinset, PFun.mem_dom]

-- theorem brtr_dom {n : ℕ} {brtr : BoundedRelationTermRestriction n} (i : Fin (brtr.dbi.schema brtr.name).card) :
--   (brtr.inFn ((brtr.dbi.schema brtr.name).fromIndex i)).Dom
--     := by
--     apply Part.dom_iff_mem.mpr
--     apply (PFun.mem_dom brtr.inFn (RelationSchema.fromIndex i)).mp
--     simp_all only [PFun.mem_dom, att_in_dom, brtr_schema_dbi_def]
--     apply RelationSchema.fromIndex_mem

-- def getMap {n : ℕ} (brtr : BoundedRelationTermRestriction n) : Fin (brtr.dbi.schema brtr.name).card → fol.Term (Variable ⊕ Fin n) :=
--   λ i => (brtr.inFn (RelationSchema.fromIndex i)).get (brtr_dom i)
