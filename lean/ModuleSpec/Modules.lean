import ModuleSpec.Relations
import ModuleSpec.Entity
import ModuleSpec.Names
import ModuleSpec.Imports
import ModuleSpec.Exports
import ModuleSpec.Utils
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
abbrev InscopeRel := Rel QName Entity

/-- A relation describing what a module exports. -/
abbrev ExportRel := Rel Name Entity

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

/-- Export relation for a type/function, without constructors or fields -/
def ExportRootJ (inscope : InscopeRel) (name : QName) (exportRel : ExportRel) : Prop :=
  (∀ expName entity,
    RelEntry.mk expName entity ∈ exportRel ↔
    expName = getQualified name ∧
    not (isCon entity) ∧
    RelEntry.mk name entity ∈ inscope)

inductive ExportItemJ : InscopeRel → ExportItem → ExportRel → Prop where
  | Single :
    ∀ inscope name exportRel,
    ExportRootJ inscope name exportRel →
    ExportItemJ inscope (ExportItem.Single name) exportRel

  | All :
    ∀ inscope name rootExport subExport,
    -- Export root as above
    ExportRootJ inscope name rootExport →
    (∀ expName entity subName,
      -- Here, entity is something owned by an entity in the
      -- root export relation. expName refers to the name of
      -- the sub-entity in the final export relation.
      RelEntry.mk expName entity ∈ subExport ↔
      expName = getQualified subName ∧
      (∃ ownEntity,
        ownEntity ∈ rng rootExport ∧
        entity ∈ owns ownEntity) ∧
      RelEntry.mk subName entity ∈ inscope) →
    exportRel = unionRels [rootExport, subExport] →
    --------------------------------------------------
    ExportItemJ inscope (ExportItem.All name) exportRel

  | Some :
    ∀ inscope name names rootExport subExport,
    -- Same structure as above
    ExportRootJ inscope name rootExport →
    (∀ expName entity subName,
      RelEntry.mk expName entity ∈ subExport ↔
      expName = getQualified subName ∧
      (∃ ownEntity,
        ownEntity ∈ rng rootExport ∧
        entity ∈ owns ownEntity) ∧
      RelEntry.mk subName entity ∈ inscope ∧
      expName ∈ names /- Only difference from [All] -/) →
    exportRel = unionRels [rootExport, subExport] →
    --------------------------------------------------
    ExportItemJ inscope (ExportItem.Some name names) _

  | Module :
    ∀ inscope modname exportRel,
    (∀ name entity,
      RelEntry.mk name entity ∈ exportRel ↔
      RelEntry.mk (QName.Qualified modname name) entity ∈ inscope ∧
      RelEntry.mk (QName.UnQualified name) entity ∈ inscope) →
    -------------------------------------------------
    ExportItemJ inscope (ExportItem.Module modname) exportRel

def export_item (inscope : InscopeRel)(exp_item : ExportItem) : ExportRel :=
  match exp_item with
  | ExportItem.Single name =>
      listToRel (List.map (RelEntry.mk (getQualified name)) (applyRel inscope name))
  | ExportItem.All name =>
      let nameEntities := applyRel inscope name;
      let ownedEntities := List.flatMap (Std.TreeSet.toList ∘ owns) nameEntities;
      mapDom getQualified
        (unionRels [
          /- All the root entities -/
          (restrictDom (.== name) inscope),
          /- All the owned entities of the root -/
          (restrictRng (λ entity => List.elem entity ownedEntities) inscope)
        ])
  | ExportItem.Some name names =>
      let nameEntities := applyRel inscope name;
      let ownedEntities := List.flatMap (Std.TreeSet.toList ∘ owns) nameEntities;
      mapDom getQualified
        (unionRels [
          /- All the root entities -/
          (restrictDom (.== name) inscope),
          /- All the owned entities of the root matching the [names] -/
          (restrictDomRng (λ n => List.elem (getQualified n) names)
                          (λ entity => List.elem entity ownedEntities)
                          inscope)
        ])
  | ExportItem.Module modName =>
    /- All the entities qualified by modName -/
    let qualEntities := restrictDom (λ n => getQualifier n == some modName) inscope;
    /- All the unqualified names -/
    let unqualEntities := restrictDom (λ n => getQualifier n == none) inscope;
    intersectRel
      (mapDom getQualified qualEntities)
      (mapDom getQualified unqualEntities)

theorem export_item_correct :
  export_item inscope exp_item = export_rel →
  ExportItemJ inscope  exp_item export_rel :=
  sorry

/-- Specify the semantics of the export list -/
inductive ExportsJ : Module → InscopeRel → ExportList → ExportRel → Prop where
    /-- If the export list is omitted, then we export all entities that the module declares locally. -/
  | Implicit :
    ∀ (m : Module),
    ------------------------------------------
    ExportsJ m _ ExportList.Implicit m.defines

    /-- If the module provides an explicit export list, then we have to form the union of all exported items.-/
  | Explicit {exports inscope} :
    ∀ (m : Module)(exportRels : List ExportRel),
    Forall2 (λ exp rel => ExportItemJ inscope exp rel) exports exportRels →
    exportRel = unionRels exportRels →
    ----------------------------------------------------------
    ExportsJ m inscope (ExportList.Explicit exports) exportRel

def exports (mod : Module)(inscope : InscopeRel)(exp_list : ExportList) : ExportRel :=
  sorry

theorem exports_correct :
  exports mod inscope exp_list = export_rel →
  ExportsJ mod inscope exp_list export_rel :=
  sorry
