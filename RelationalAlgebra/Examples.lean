import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Tactics

open RM

-- Required type definitions for these examples to work (@TODO: See if this can be done in a prettier way)
-- inductive Attribute
-- | Name | Age | Salary
-- deriving DecidableEq

-- inductive RelationName
-- | Employee | Department
-- deriving DecidableEq

-- abbrev Value := String

-- Example values
def Alice : Value := "Alice"
def Bob : Value := "Bob"
def Charlie : Value := "Bob"
def age25 : Value := "25"
def age30 : Value := "30"
def age35 : Value := "35"
def salary50000 : Value := "50000"
def salary60000 : Value := "60000"
def salary70000 : Value := "70000"

-- Example relation schema
def EmployeeSchema : RelationSchema := {.Name, .Age, .Salary}
def DepartmentSchema : RelationSchema := {.Name}

-- Example tuples
def tuple1 : Tuple :=
    fun attr => -- Destructure the Subtype {a : Attribute // a ∈ EmployeeSchema}
      if attr = .Name then Alice
      else if attr = .Age then age25
      else if attr = .Salary then salary50000
      else Part.none

def tuple2 : Tuple :=
  fun attr =>
    if attr = .Name then Bob
    else if attr = .Age then age30
    else if attr = .Salary then salary60000
    else Part.none

def tuple3 : Tuple :=
  fun attr =>
    if attr = .Name then Charlie
    else if attr = .Age then age35
    else if attr = .Salary then salary70000
    else Part.none

-- Example relation instance (a set of tuples)
def EmployeeInstance : RelationInstance := ⟨
  EmployeeSchema,
  {tuple1, tuple2, tuple3},
  by unfold EmployeeSchema tuple1 tuple2 tuple3; decide_valid_schema
⟩

-- Example tuples for Department relation
def deptTuple1 : Tuple :=
  fun attr =>
    if attr = .Name then Alice
    else Part.none

def deptTuple2 : Tuple :=
  fun attr =>
    if attr = .Name then Bob
    else Part.none

-- Example relation instance for Department
def DepartmentInstance : RelationInstance := ⟨
  DepartmentSchema,
  {deptTuple1, deptTuple2},
  by unfold DepartmentSchema deptTuple1 deptTuple2; decide_valid_schema
⟩

-- Example database schema
def MyDatabaseSchema : DatabaseSchema
  | .Employee => EmployeeSchema
  | .Department => DepartmentSchema

def MyDatabaseInstanceMap : RelationName → RelationInstance
  | .Employee => EmployeeInstance
  | .Department => DepartmentInstance

-- Example database instance
def MyDatabaseInstance : DatabaseInstance := ⟨
  MyDatabaseSchema,
  MyDatabaseInstanceMap,
  by unfold MyDatabaseInstanceMap; decide_valid_database_schema
⟩
