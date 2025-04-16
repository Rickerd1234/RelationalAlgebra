import RelationalAlgebra.RelationalModel

open RM

macro "decide_valid_database_schema" : tactic => `(tactic| (intro rel; split <;> rfl))

syntax "decide_valid_schema" : tactic
syntax "split_schema" : tactic
syntax "decide_valid_schema_set" : tactic
syntax "decide_valid_schema_singleton" : tactic

macro_rules
| `(tactic| decide_valid_schema) => `(tactic| simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]; split_schema)
| `(tactic| split_schema) => `(tactic| apply And.intro <;> (first | split_schema | decide_valid_schema_set | decide_valid_schema_singleton))
| `(tactic| decide_valid_schema_set) => `(tactic| (
  simp_all only [Part.coe_some, dite_eq_ite, PFun.dom_mk]
  ext x : 1
  simp_all only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  apply Iff.intro
  · intro a
    split at a
    next h =>
      subst h
      simp_all only [Part.some_dom, reduceCtorEq, or_self, or_false]
    next h =>
      split at a
      next h_1 =>
        subst h_1
        simp_all only [Part.some_dom, reduceCtorEq, not_false_eq_true, or_false, or_true]
      next h_1 =>
        split at a
        next h_2 =>
          subst h_2
          simp_all only [Part.some_dom, reduceCtorEq, not_false_eq_true, or_true]
        next h_2 => simp_all only [Part.not_none_dom]
  · intro a
    cases a with
    | inl h =>
      subst h
      simp_all only [↓reduceIte, Part.some_dom]
    | inr h_1 =>
      cases h_1 with
      | inl h =>
        subst h
        simp_all only [reduceCtorEq, ↓reduceIte, Part.some_dom]
      | inr h_2 =>
        subst h_2
        simp_all only [reduceCtorEq, ↓reduceIte, Part.some_dom]
))
| `(tactic| decide_valid_schema_singleton) => `(tactic| (
  simp_all only [Part.coe_some, PFun.dom_mk]
  ext x : 1
  simp_all only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  apply Iff.intro
  · intro a
    split at a
    next h =>
      subst h
      simp_all only [Part.some_dom]
    next h => simp_all only [Part.not_none_dom]
  · intro a
    subst a
    simp_all only [↓reduceIte, Part.some_dom]
))
