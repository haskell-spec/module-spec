import ModuleSpec.Names

inductive ImportSubSpec where
  | AllSubs
  | Subs (l : List Name)

-- EntSpec
structure ImportItem where
  name : Name
  sub : Option ImportSubSpec

def ImportList := List ImportItem
