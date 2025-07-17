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

def Query.schema : (q : Query) → (dbs : DatabaseSchema) → RelationSchema
  | .R rn => λ dbs => dbs rn
  | .s _ _ _ sq => sq.schema
  | .p rs _ => λ _ => rs
  | .j q1 q2 => λ dbs => q1.schema dbs ∪ q2.schema dbs
  | .r f sq => λ dbs => renameSchema (sq.schema dbs) f
  -- | .u q1 _ => q1.schema
  -- | .d q1 _ => q1.schema

def Query.isWellTyped (dbs : DatabaseSchema) (q : Query) : Prop :=
  match q with
  | .R _ => (True)
  | .s a b _ sq => sq.isWellTyped dbs ∧ a ∈ sq.schema dbs -- ∧ @TODO Requirement for b in case of attribute
  | .p rs sq => sq.isWellTyped dbs ∧ rs ⊆ sq.schema dbs
  | .j q1 q2 => q1.isWellTyped dbs ∧ q2.isWellTyped dbs
  | .r f sq => sq.isWellTyped dbs ∧ f.Surjective
  -- | .u q1 q2 => q1.isWellTyped dbs ∧ q2.isWellTyped dbs ∧ q1.schema dbs = q2.schema dbs
  -- | .d q1 q2 => q1.isWellTyped dbs ∧ q2.isWellTyped dbs ∧ q1.schema dbs = q2.schema dbs

def Query.evaluateT (dbi : DatabaseInstance) (q : Query) : Set Tuple :=
  match q with
  | .R rn => (dbi.relations rn).tuples
  | .s a b i sq => selectionT (sq.evaluateT dbi) a b i
  | .p rs sq => projectionT (sq.evaluateT dbi) rs
  | .j q1 q2 => joinT (q1.evaluateT dbi) (q2.evaluateT dbi)
  | .r f sq => renameT (sq.evaluateT dbi) f
  -- | .u q1 q2 => unionT (q1.evaluateT dbi) (q2.evaluateT dbi)
  -- | .d q1 q2 => diffT (q1.evaluateT dbi) (q2.evaluateT dbi)

def Query.evaluate (dbi : DatabaseInstance) (q : Query) (h : q.isWellTyped dbi.schema) : RelationInstance :=
  ⟨
    q.schema dbi.schema,
    q.evaluateT dbi,
    by sorry
  ⟩



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
  (.j (.R "R1") (.R "R2"))

theorem hj {dbi} : j.isWellTyped dbi := by
  simp_all [j, Query.isWellTyped]

#simp [Query.evaluate, Query.schema, j, dbI, relS, relS2] (j.schema dbI.schema)
#simp [Query.evaluate, Query.evaluateT, j, dbI, relI, relI2, joinT, tup1, tup2, tup3, tupA, tupB, tupC] (j.evaluate dbI hj).tuples
