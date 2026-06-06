-- Syntax of Export Lists

import ModuleSpec.Names

inductive ExportSubSpec where
  | AllSubs
  | Subs : List Name → ExportSubSpec

inductive EntSpec where
  | Ent : QName → Option (ExportSubSpec) → EntSpec

inductive ExpListEntry where
  | EntExp : EntSpec → ExpListEntry
  | ModuleExp : ModName → ExpListEntry

def ExportList := List ExpListEntry
