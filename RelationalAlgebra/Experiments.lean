import RelationalAlgebra.Data

-- Define a relation schema
def personSchema : RelationSchema := {
  attributes := [("name", strDomain), ("age", intDomain), ("id", mixDomain)],
  nodup := by decide
}

-- Define a relation type (name + schema)
def personRelation : RelationInstance personSchema := {
  {
    values := [("name", .Str "value"), ("age", .Int 3), ("id", .Str "3")]
    inSchema := by decide
    coverSchema := by decide
    nodup := by decide
  },
  {
    values := [("name", .Str "value"), ("age", .Int 3), ("id", .Int 3)]
    inSchema := by decide
    coverSchema := by decide
    nodup := by decide
  },
  {
    values := [("name", .Str "3"), ("age", .Int 3), ("id", .Str "3")]
    inSchema := by decide
    coverSchema := by decide
    nodup := by decide
  }
}

-- Define a relation schema
def teamSchema : RelationSchema := {
  attributes := [
    ("name", strDomain),
    ("player", int?Domain),
    ("count", intDomain),
    -- ("coverSchemaFail", intDomain)

  ],
  nodup := by decide
}

-- Define a relation type (name + schema)
def teamRelation : RelationInstance teamSchema := {
  {
    values := [
      ("name", .Str "value"),
      ("player", .Int 3),
      ("count", .Int 3)
    ]
    coverSchema := by decide
    inSchema := by decide
    nodup := by decide
  },
  {
    values := [
      ("name", .Str "value"),
      ("player", .Null),
      ("count", .Int 3)
    ]
    coverSchema := by decide
    inSchema := by decide
    nodup := by decide
  },
  {
    values := [
      ("name", .Str "3"),
      ("player", .Int 3),
      ("count", .Int 3)
      -- ("inSchemaFail", .Int 4)
    ]
    coverSchema := by decide
    inSchema := by decide
    nodup := by decide
  }
}

def dbSchema : DatabaseSchema := {
  relations := [
    ("person", personSchema),
    ("team", teamSchema),
    -- ("coverSchemaFail", teamSchema)
  ],
  nodup := by decide
}

def dbInstance : DatabaseInstance dbSchema := {
  relations := [
    ⟨"person", personRelation⟩,
    ⟨"team", teamRelation⟩,
    -- ⟨"inSchemaFail", ()⟩,
  ],
  inSchema := by decide
  coverSchema := by decide
  nodup := by decide
}
