import ModuleSpec.Names

inductive ImportSubSpec where
  | AllSubs
  | Subs (l : List Name)

-- EntSpec
structure ImportItem where
  name : Name
  sub : Option ImportSubSpec

structure Import where
  qualified : Bool
  source : ModName
  as : ModName
  hiding_ : Bool
  items : List ImportItem
