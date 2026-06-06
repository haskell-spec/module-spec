import ModuleSpec.Names
import ModuleSpec.EntSpec

inductive SubSpec where
  | AllSubs
  | Subs (l : List Name)

-- EntSpec
structure ImportItem where
  name : Name
  sub : Option SubSpec

def ExportList := List ImportItem
