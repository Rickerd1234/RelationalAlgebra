import RelationalAlgebra.Examples
import RelationalAlgebra.Util.Util
import RelationalAlgebra.FOL.Evaluate

-- Operations for BoundedFormula
-- AND: ⊓
-- OR: ⊔
-- NOT: ∼
-- IMP: ⟹
-- BIIMP: ⇔
-- EX: .ex
-- ALL: .all


namespace FOL

open FirstOrder RM

open FOL Language

abbrev exFol := (fol exDatabase.schema)

def x : exFol.Term (String ⊕ Fin 0) := outVar "x"
def y : exFol.Term (String ⊕ Fin 0) := outVar "y"
def z : exFol.Term (String ⊕ Fin 1) := inVar 0

-- Explore formula concepts
def n_xy : exFol.BoundedFormula String 0 := ∼(x =' y)

def ex_n_xy_or_yz : exFol.Formula String := .ex ((n_xy.liftAt 1 0) ⊔ (y.liftAt 1 0) =' z)

def ex_n_xy_and_yz : exFol.Formula String := .ex ((n_xy.liftAt 1 0) ⊓ (y.liftAt 1 0) =' z)

def all_xz_or_yz : exFol.Formula String := .ex ((y.liftAt 1 0) =' z ⟹ ∼((x.liftAt 1 0) =' z))

@[simp]
def v' : String → String
  | "x" => "1"
  | "y" => "Anna"
  | _ => ""

example [struc: exFol.Structure (String)] : ex_n_xy_or_yz.Realize v' := by
  simp only [Formula.Realize, ex_n_xy_or_yz, n_xy, x, y, z, BoundedFormula.realize_ex]
  simp [BoundedFormula.realize_sup, BoundedFormula.realize_liftAt_one_self, true_or, exists_const]

example [struc: exFol.Structure (String)] : ex_n_xy_and_yz.Realize v' := by
  simp only [Formula.Realize, ex_n_xy_and_yz, n_xy, x, y, z, BoundedFormula.realize_ex]
  use "Anna"
  simp
  rfl

example [struc: exFol.Structure (String)] : all_xz_or_yz.Realize v' := by
  simp only [Formula.Realize, all_xz_or_yz, x, y, z, outVar, inVar]
  simp
  use ""
  simp [Term.liftAt, Fin.snoc]


@[simp]
def v := PFun.res v' {"x", "y"}

-- Relation with variables
def F : Query exDatabase.schema := (.R "employee" [outVar "x", outVar "y"].get)

example (h : a ∈ exDatabase.schema "employee") :
  RelationSchema.index h < (exDatabase.schema "employee").card := by
    simp
    exact (RelationSchema.index h).isLt

example [struc: folStruc exDatabase] : F.RealizeMin exDatabase v := by
  -- Unfold query
  simp only [Query.RealizeMin, BoundedQuery.Realize, F, BoundedQuery.toFormula, BoundedFormula.realize_rel]

  simp [BoundedQuery.schema, BoundedQuery.toFormula, Relations.boundedFormula]

  refine Exists.intro (Set.toFinset_inj.mp rfl) ?_

  -- @TODO: Generalize this proof
  rw [← fol.Rel, folStruc_apply_RelMap exDatabase]
  simp_all only [exDatabase, exRelationDepartment, exRelationEmployee, exRelationEmployeeDepartment,
    String.reduceEq, implies_true, exDatabase.eq_1, exRelationDepartment.eq_1,
    exRelationEmployee.eq_1, exRelationEmployeeDepartment.eq_1, ArityToTuple.def_dite,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  apply Or.inl
  ext a b
  split
  . rename_i h
    have h' : a ∈ exDatabase.schema "employee" := by exact h
    have h'' := RelationSchema.index?_isSome.mpr h'
    have h''' := RelationSchema.index?_isSome_eq_iff.mp h''
    simp_all
    sorry



  . grind


-- Relation with a free variable
def inG : String →. exFol.Term (String ⊕ Fin 1)
  | "0" => .some (outVar "x")
  | "1" => .some (inVar 0)
  | _ => .none

theorem inG_dom : inG.Dom = ({"0", "1"} : Finset String) := by unfold inG; aesop

def G : Query := .ex (.R brtr_G)
theorem v_sat_G [struc: folStruc] : G.Realize dbI v := by
  -- Unfold query
  simp only [Query.Realize, BoundAttributeRealize, G, BoundedQuery.toFormula, BoundedFormula.realize_ex]

  apply And.intro
  -- Fill in inVar value
  . use 22
    apply And.intro (by simp_all [dbI, DatabaseInstance.domain]; use "R1"; use 1; use tup2; tauto)

    simp only [BoundedQuery.RealizeDom, BoundedQuery.Realize, G, BoundedQuery.toFormula, BoundedFormula.realize_ex]
    sorry
    -- apply And.intro

    -- . -- Use relation structure
    --   refine (folStruc.RelMap_R dbI "R1" ?_).mp ?_

    --   -- Find specific equivalent tuple
    --   apply Or.inr
    --   apply Or.inl

    --   -- Break down assignmentToTuple proof
    --   rw [arityToTuple_def]
    --   intro i
    --   simp [tup2]

    --   -- Proof all goals
    --   split
    --   all_goals (try simp_all [getMap, v, outVar, inVar]; try rfl)
    --   next x x_1 x_2 =>
    --     have z := RelationSchema.fromIndex_mem i
    --     simp_all [dbI, relI, relS]
    --   next => simp [dbI, relI]
    -- . rw [PFun.ran]
    --   simp_all [dbI, DatabaseInstance.domain, relI, v, tup1, tup2, tup3]
    --   apply And.intro
    --   · intro a x h
    --     split at h
    --     next x =>
    --       simp_all only [Part.mem_some_iff]
    --       subst h
    --       use "R1"; use 0; use tup2; tauto
    --     next x =>
    --       simp_all only [Part.mem_some_iff]
    --       subst h
    --       use "R1"; use 1; use tup2; tauto
    --     next x_1 x_2 x_3 => simp_all only [imp_false, Part.not_mem_none]
    --   · rw [PFun.ran]
    --     simp_all only [Set.setOf_subset_setOf, forall_exists_index]
    --     simp_all [Fin.snoc]
    --     use "R1"; use 1; use tup2; tauto

  . apply And.intro
    · simp [dbI, PFun.ran, DatabaseInstance.domain, relI, v]
      intro a x h
      split at h
      next x =>
        simp_all only [Part.mem_some_iff]
        subst h
        use "R1"
        simp [tup2]
        use 0
        simp_all
      next x =>
        simp_all only [Part.mem_some_iff]
        subst h
        use "R1"
        simp [tup2]
        use 1
        simp_all
      next x_1 x_2 x_3 => simp_all only [imp_false, Part.not_mem_none]
    · simp [PFun.ran]



-- Relation with two free variables
def tsH : Fin 2 → exFol.Term (String ⊕ Fin 2) :=
  [(inVar 1), (inVar 0)].get

def H : Query exDatabase.schema := .ex (.ex (.R "employee" tsH))
example [struc: folStruc exDatabase] : H.RealizeMin exDatabase v := by
  -- Unfold query
  simp [Query.Realize, BoundedQuery.Realize, BoundedQuery.toFormula, H]


  -- Split goal into sat and active domain parts
  apply And.intro
  -- Fill in inVar values
  · sorry
    -- use Part.some 22
    -- use Part.some 21

    -- -- Use relation structure
    -- refine (folStruc.RelMap_R dbI "R1" ?_).mp ?_

    -- -- Find specific equivalent tuple
    -- apply Or.inr
    -- apply Or.inl


    -- -- Break down assignmentToTuple proof
    -- rw [assignmentToTuple_def]
    -- intro i
    -- simp [tup2]

    -- -- Proof all goals
    -- split
    -- all_goals (try simp_all [getMap, v, outVar, inVar]; try rfl)
    -- next x x_1 x_2 =>
    --   have z := RelationSchema.fromIndex_mem i
    --   simp_all [dbI, relI, relS]
    -- next => simp [dbI, relI]

  -- Proof active domain semantics
  · apply And.intro
    · simp [dbI, PFun.ran, DatabaseInstance.domain, relI, v]
      intro a x h
      split at h
      next x =>
        simp_all only [Part.mem_some_iff]
        subst h
        use "R1"
        simp [tup1, tup2, tup3, RelationInstance.tuples]
        use 0
        simp
      next x =>
        simp_all only [Part.mem_some_iff]
        subst h
        use "R1"
        simp [tup1, tup2, tup3, RelationInstance.tuples]
        use 1
        simp
      next x_1 x_2 x_3 => simp_all only [imp_false, Part.not_mem_none]
    . simp [PFun.ran]



def outG : Attribute →. Variable
  | 1 => "x"
  | _ => .none

def t : EvaluableQuery (dbI) :=
  ⟨
    G,
    outG,
    by
      have h : outG.Dom = ({1} : Finset Attribute) := by unfold outG; aesop
      rw [h]
      exact FinsetCoe.fintype ?_,
    by
      simp [BoundedQuery.attributesInQuery, G, brtr_G, inG, outG, RelationTermRestriction.outVars, Language.var, outVar?, RelationTermRestriction.vars, PFun.ran]
      ext
      simp_all only [Set.mem_toFinset, Set.mem_setOf_eq, Fin.isValue, Finset.mem_filterMap, outVar?]
      apply Iff.intro
      · intro a
        obtain ⟨w, h⟩ :=Attribute
        split at h
        next x_1 =>
          simp_all only [Part.mem_some_iff, Fin.isValue]
          subst h
          use outVar "x"
          simp [outVar]
          use 0
          simp
        next x_1 x_2 => simp_all only [imp_false, Part.not_mem_none]
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        obtain ⟨w_1, h⟩ := left
        split at right
        next x_1 x_2 =>
          split at h
          next x_3 =>
            simp_all only [Sum.getLeft?_eq_some_iff, Part.mem_some_iff]
            subst right
            use 1
            simp_all [outVar]
          next x_3 =>
            simp_all only [Sum.getLeft?_eq_some_iff, Fin.isValue, Part.mem_some_iff]
            subst right
            use 1
            simp_all [inVar]
          next x_3 x_4 x_5 => simp_all only [Sum.getLeft?_eq_some_iff, imp_false, Part.not_mem_none]
        next x_1 x_2 =>
          split at h
          next x_3 => simp_all only [imp_false, Sum.forall, reduceCtorEq]
          next x_3 => simp_all only [imp_false, Sum.forall, reduceCtorEq]
          next x_3 x_4 x_5 => simp_all only [imp_false, Sum.forall, reduceCtorEq]
  ⟩

theorem v_to_tup_in_t : VariableAssignmentToTuple t v = λ x => match x with | 1 => .some 21 | _ => .none := by
  ext a val
  apply Iff.intro
  · intro a_1
    split
    next x =>
      unfold VariableAssignmentToTuple v at a_1
      simp_all only [t, outG, Part.coe_some, Part.bind_some, Part.mem_some_iff]
    next x x_1 =>
      simp_all only [imp_false, Part.not_mem_none]
      unfold VariableAssignmentToTuple v at a_1
      simp_all only [t, outG, Part.coe_some, Part.bind_none, Part.not_mem_none]
  · intro a_1
    split at a_1
    next x =>
      simp_all only [Part.mem_some_iff]
      subst a_1
      unfold VariableAssignmentToTuple v
      simp_all only [t, outG, Part.coe_some, Part.mem_bind_iff, Part.mem_some_iff, exists_eq_left]
    next x x_1 => simp_all only [imp_false, Part.not_mem_none]

example [folStruc] : t.evaluate.tuples = ({λ x => match x with | 1 => .some 21 | _ => .none} : Set Tuple) := by
  unfold EvaluableQuery.evaluate EvaluableQuery.evaluateT VariableAssignmentToTuple
  ext t;
  simp_all only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  have z1 : FOL.t.query = G := by rfl
  have z2 := v_to_tup_in_t
  have z3 := v_sat_G
  simp_all only
  apply Iff.intro
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    have z4 : w = v := by sorry
    subst right
    ext a v'
    simp_all only [Part.mem_bind_iff]
    apply Iff.intro
    · intro a_1
      obtain ⟨w_1, h⟩ := a_1
      obtain ⟨left_1, right⟩ := h
      split
      all_goals simp_all [v, t, outG]
    · intro a_1
      split at a_1
      next x => simp_all [Part.mem_some_iff, v, t, outG]
      next x x_1 => simp_all only [imp_false, Part.not_mem_none]
  · intro a
    subst a
    use v
    unfold VariableAssignmentToTuple at z2
    simp_all only [and_self]
