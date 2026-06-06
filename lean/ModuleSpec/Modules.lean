import ModuleSpec.Relations
import ModuleSpec.Entity
import ModuleSpec.Names
import Std.Data.HashMap

-- Syntax of Modules

structure Module where
  name : ModName
  imports : Unit -- TODO
  exports : Unit -- TODO

def InscopeRel := Rel QName Entity

def ExportRel := Rel Name Entity

def ExportEnv := Std.HashMap ModName ExportRel


/-- Specify the semantics of a single import statement -/
inductive ImportJ : ExportEnv → Import → InscopeRel → Prop where
  -- TODO

/-- Specify the semantics of the export list -/
inductive ExportsJ : InscopeRel → Exports → ExportRel → Prop where
  -- TODO
