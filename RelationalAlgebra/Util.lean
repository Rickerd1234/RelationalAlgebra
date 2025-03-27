import RelationalAlgebra.RelationalModel

open RM

section empty

@[simp]
def emptyInst {schema : RelationSchema} : RelationInstance := ⟨
  schema,
  ∅,
  by simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]
⟩

end empty
