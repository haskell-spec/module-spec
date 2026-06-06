import ModuleSpec.Relations
import ModuleSpec.Entity
import ModuleSpec.Names
import ModuleSpec.Imports
import ModuleSpec.Exports
import Std.Data.HashMap

-- Syntax of Modules

structure Module where
  name : ModName
  imports : ImportList -- TODO
  exports : ExportList -- TODO

def InscopeRel := Rel QName Entity

def ExportRel := Rel Name Entity

def ExportEnv := Std.HashMap ModName ExportRel


/-- Specify the semantics of a single import statement -/
inductive ImportJ : ExportEnv → ImportItem → InscopeRel → Prop where
  -- TODO

/-- Specify the semantics of the export list -/
inductive ExportsJ : InscopeRel → ExportList → ExportRel → Prop where
  -- TODO
