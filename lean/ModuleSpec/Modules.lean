import ModuleSpec.Relations
import ModuleSpec.Entity
import ModuleSpec.Names
import ModuleSpec.Imports
import ModuleSpec.Exports
import Std.Data.HashMap

-- Syntax of Modules

/-- A single Haskell module. -/
structure Module where
  /-- The name of the module. -/
  name : ModName
  /-- The list of import statements. -/
  imports : ImportList
  /-- The export list -/
  exports : Option ExportList
  /-- The local definitions of the module. -/
  defines : Rel Name Entity


/-- A relation describing what is currently in scope. -/
def InscopeRel := Rel QName Entity

/-- A relation describing what a module exports. -/
def ExportRel := Rel Name Entity

def ExportEnv := Std.HashMap ModName ExportRel


/-- Specify the semantics of a single import statement -/
inductive ImportJ : ExportEnv → ImportItem → InscopeRel → Prop where
  -- TODO

/-- Specify the semantics of the export list -/
inductive ExportsJ : InscopeRel → ExportList → ExportRel → Prop where
  -- TODO
