-- Syntax of Export Lists

import ModuleSpec.Names

inductive SubSpec where
  | AllSubs
  | Subs : List Name → SubSpec

inductive EntSpec where
  | Ent : QName → Option (SubSpec) → EntSpec

inductive ExpListEntry where
  | EntExp : EntSpec → ExpListEntry
  | ModuleExp : ModName → ExpListEntry
