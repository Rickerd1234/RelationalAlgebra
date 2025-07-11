import RelationalAlgebra.RA.RelationalAlgebra

open RM

inductive Query : Type
  | R: RelationName → Query
  | s: Attribute → (Attribute ⊕ Value) → Bool → Query → Query
  | p: RelationSchema → Query → Query
  | j: Query → Query → Query
  | r: (Attribute → Attribute) → Query → Query
  -- | u: Query → Query → Query
  -- | d: Query → Query → Query

def Query.schema : (q : Query) → (dbi : DatabaseInstance) → RelationSchema
  | .R rn => λ dbi => dbi.schema rn
  | .s _ _ _ sq => sq.schema
  | .p rs _ => λ _ => rs
  | .j q1 q2 => λ dbi => q1.schema dbi ∪ q2.schema dbi
  | .r f sq => λ dbi => renameSchema (sq.schema dbi) f
  -- | .u q1 _ => q1.schema
  -- | .d q1 _ => q1.schema

def Query.isSafeRec (dbi : DatabaseInstance) (q : Query) : (RelationSchema × Prop) :=
  match q with
  | .R _ => (q.schema dbi, True)
  | .s _ _ _ sq => sq.isSafeRec dbi -- @TODO: Verify if this requires any safety checks
  | .p rs sq => (q.schema dbi, (sq.isSafeRec dbi).2 ∧ rs ⊆ (sq.schema dbi))
  | .j q1 q2 => (q.schema dbi, (q1.isSafeRec dbi).2 ∧ (q2.isSafeRec dbi).2)
  | .r f sq => (q.schema dbi, (sq.isSafeRec dbi).2 ∧ f.Surjective)
  -- | .u q1 q2 => (q.schema dbi, (q1.isSafeRec dbi).2 ∧ (q2.isSafeRec dbi).2 ∧ q1.schema dbi = q2.schema dbi)
  -- | .d q1 q2 => (q.schema dbi, (q1.isSafeRec dbi).2 ∧ (q2.isSafeRec dbi).2 ∧ q1.schema dbi = q2.schema dbi)

def Query.isSafe (dbi : DatabaseInstance) (q : Query): Prop := (q.isSafeRec dbi).2

def Query.evaluate (dbi : DatabaseInstance) (q : Query) (h : q.isSafe dbi) : RelationInstance :=
  match q with
  | .R rn => dbi.relations rn
  | .s a b i sq => selection (sq.evaluate dbi (by simp_all [isSafe, isSafeRec])) a b i
  | .p rs sq => projection (sq.evaluate dbi (by simp_all [isSafe, isSafeRec])) rs (by sorry)
  | .j q1 q2 => join (q1.evaluate dbi (by simp_all [isSafe, isSafeRec])) (q2.evaluate dbi (by simp_all [isSafe, isSafeRec]))
  | .r f sq => rename (sq.evaluate dbi (by simp_all [isSafe, isSafeRec])) f (by simp_all [isSafe, isSafeRec])
  -- | .u q1 q2 => union (q1.evaluate dbi (by simp_all [isSafe, isSafeRec])) (q2.evaluate dbi (by simp_all [isSafe, isSafeRec])) (by sorry)
  -- | .d q1 q2 => diff (q1.evaluate dbi (by simp_all [isSafe, isSafeRec])) (q2.evaluate dbi (by simp_all [isSafe, isSafeRec])) (by sorry)



def tup1 : Tuple
  | 0 => some 11
  | 1 => some 12
  | _ => Part.none

def tup2 : Tuple
  | 0 => some 21
  | 1 => some 22
  | _ => Part.none

def tup3 : Tuple
  | 0 => some 31
  | 1 => some 32
  | _ => Part.none

def tupA : Tuple
  | 1 => some 11
  | 2 => some 12
  | _ => Part.none

def tupB : Tuple
  | 1 => some 21
  | 2 => some 22
  | _ => Part.none

def tupC : Tuple
  | 1 => some 31
  | 2 => some 32
  | _ => Part.none

def relS : RelationSchema := {0, 1}
def relS2 : RelationSchema := {1, 2}

def relI : RelationInstance := ⟨
  relS,
  {tup1, tup2, tup3},
  by
    simp [relS, tup1, tup2, tup3, PFun.Dom]
    aesop
⟩
def relI2 : RelationInstance := ⟨
  relS2,
  {tupA, tupB, tupC},
  by
    simp [relS2, tupA, tupB, tupC, PFun.Dom]
    aesop
⟩

def dbI : DatabaseInstance := ⟨
  λ x => match x with
  | "R1" => relS
  | "R2" => relS2
  | _ => ∅,
  λ x => match x with
  | "R1" => relI
  | "R2" => relI2
  | _ => ∅r ∅,
  by
    intro rel
    simp_all only [RelationInstance.empty]
    aesop
⟩

def j : Query :=
  .j (.R "R1") (.R "R2")

#simp [Query.evaluate, Query.schema, j, dbI, join, relI, relI2, relS, relS2, tup1, tup2, tup3, tupA, tupB, tupC] (j.schema dbI)
