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
  imports : List Import
  /-- The export list -/
  exports : Option ExportList
  /-- The local definitions of the module. -/
  defines : Rel Name Entity


/-- A relation describing what is currently in scope. -/
def InscopeRel := Rel QName Entity

/-- A relation describing what a module exports. -/
def ExportRel := Rel Name Entity

def ExportEnv := Std.HashMap ModName ExportRel

/-
Semantic of Imports
-/

/-- Specify the semantics of a single `ImportItem` -/
inductive ImportItemJ : ExportEnv → ImportItem → InscopeRel → Prop where
  | Single :
    ∀ exports name,
    -- TODO
    ----------------------------------------------
    ImportItemJ exports (ImportItem.Single name) _

  | All :
    ∀ exports name,
    -- TODO
    -------------------------------------------
    ImportItemJ exports (ImportItem.All name) _

  | Some :
    ∀ exports name names,
    -- TODO
    --------------------------------------------------
    ImportItemJ exports (ImportItem.Some name names) _

/-- Specify the semantics of a single import statement -/
inductive ImportJ : ExportEnv → Import → InscopeRel → Prop where
  | Hiding :
    ∀ qual modname asname items,
    -- TODO
    ------------------------------------------------------------
    ImportJ exports (Import.mk qual modname asname true items) _

  | Exposing :
    ∀ qual modname asname items,
    -- TODO
    -------------------------------------------------------------
    ImportJ exports (Import.mk qual modname asname false items) _


/-
Semantic of Exports
-/

inductive ExportItemJ : InscopeRel → ExportItem → ExportRel → Prop where
  | Single :
    ∀ inscope name,
    -- TODO
    ----------------------------------------------
    ExportItemJ inscope (ExportItem.Single name) _

  | All :
    ∀ inscope name,
    -- TODO
    -------------------------------------------
    ExportItemJ inscope (ExportItem.All name) _

  | Some :
    ∀ inscope name names,
    -- TODO
    --------------------------------------------------
    ExportItemJ inscope (ExportItem.Some name names) _

  | Module :
    ∀ inscope modname,
    -- TODO
    -------------------------------------------------
    ExportItemJ inscope (ExportItem.Module modname) _

/-- Specify the semantics of the export list -/
inductive ExportsJ : Module → InscopeRel → ExportList → ExportRel → Prop where
    /-- If the export list is omitted, then we export all entities that the module declares locally. -/
  | Implicit :
    ∀ (m : Module),
    ------------------------------------------
    ExportsJ m _ ExportList.Implicit m.defines

    /-- If the module provides an explicit export list, then we have to form the union of all exported items.-/
  | Explicit {exports inscope} :
    -- TODO:
    ∀ (m : Module),
    ∀ (exportRels : List ExportRel),
    List.length exportRels = List.length exports →
    (∀ exportItem exportRel,
      (exportItem, exportRel) ∈ List.zip exports exportRels →
      ExportItemJ inscope exportItem exportRel) →
    ExportsJ m inscope (ExportList.Explicit exports) (unionRels exportRels)
