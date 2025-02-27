import RelationalAlgebra.RelationalModel

def union {relSch : RelationSchema} (relI relI' : RelationInstance relSch) := Set.union relI relI'

theorem union_comm {relSch : RelationSchema} (relI relI' : RelationInstance relSch)
  : union relI relI' = union relI' relI := by exact Set.union_comm relI relI'
