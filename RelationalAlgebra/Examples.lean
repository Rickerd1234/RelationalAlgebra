import RelationalAlgebra.RelationalModel
import RelationalAlgebra.Coercions
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

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
def age25 : Value := "25"
def age30 : Value := "30"
def salary50000 : Value := "50000"
def salary60000 : Value := "60000"

-- Example relation schema
def EmployeeSchema : RelationSchema := {.Name, .Age, .Salary}
def DepartmentSchema : RelationSchema := {.Name}

-- Example tuples
def tuple1 : Tuple EmployeeSchema :=
  fun ⟨attr, h⟩ => -- Destructure the Subtype {a : Attribute // a ∈ EmployeeSchema}
    if _ : attr = .Name then Alice
    else if _ : attr = .Age then age25
    else if _ : attr = .Salary then salary50000
    else absurd h (by simp [EmployeeSchema,  *])

def tuple2 : Tuple EmployeeSchema :=
  fun ⟨attr, h⟩ =>
    if _ : attr = .Name then Bob
    else if _ : attr = .Age then age30
    else if _ : attr = .Salary then salary60000
    else absurd h (by simp [EmployeeSchema, *])

-- Example relation instance (a set of tuples)
def EmployeeInstance : RelationInstance EmployeeSchema := {tuple1, tuple2}

-- Example tuples for Department relation
def deptTuple1 : Tuple DepartmentSchema :=
  fun ⟨attr, h⟩ =>
    if h1 : attr = .Name then Alice
    else absurd h (by simp [DepartmentSchema, *])

def deptTuple2 : Tuple DepartmentSchema :=
  fun ⟨attr, h⟩ =>
    if h1 : attr = .Name then Bob
    else absurd h (by simp [DepartmentSchema, *])

-- Example relation instance for Department
def DepartmentInstance : RelationInstance DepartmentSchema := {deptTuple1, deptTuple2}

-- Example database schema
def MyDatabaseSchema : DatabaseSchema
  | RelationName.Employee => EmployeeSchema
  | RelationName.Department => DepartmentSchema

-- Example database instance
def MyDatabaseInstance : DatabaseInstance MyDatabaseSchema
  | RelationName.Employee => EmployeeInstance
  | RelationName.Department => DepartmentInstance
