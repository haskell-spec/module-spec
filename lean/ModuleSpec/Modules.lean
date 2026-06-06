-- Syntax of Modules
import ModuleSpec.Names

inductive SubSpec where
  | AllSubs
  | Subs : List Name → SubSpec

inductive EntExp where
  | Ent : QName → Option (SubSpec) → EntExp

inductive ExpListEntry where
  | EntExp : EntSpec → ExpListEntry
  | ModuleExp : ModName → ExpListEntry
