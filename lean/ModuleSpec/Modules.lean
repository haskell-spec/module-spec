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
  exports : ExportList
  /-- The local definitions of the module. -/
  defines : FinRel Name Entity

/-- A relation describing what is currently in scope. -/
abbrev InscopeRel := FinRel QName Entity

abbrev UnqInscopeRel := FinRel Name Entity

/-- A relation describing what a module exports. -/
abbrev ExportRel := FinRel Name Entity

abbrev ExportEnv := Std.HashMap ModName ExportRel

/-
Semantic of Imports
-/

/-- Specify the semantics of a single `ImportItem` -/
inductive ImportItemJ : ExportRel → ImportItem → UnqInscopeRel → Prop where
  | Single :
    ∀ exportRel name entity inscopeRel,
    (name, entity) ∈ exportRel →
    inscopeRel = { (name, entity) } →
    ---------------------------------------------------------------------------
    ImportItemJ exportRel (ImportItem.Single name) inscopeRel

  | All :
    ∀ exportRel name entity subImport inscopeRel,
    (name, entity) ∈ exportRel →
    (∀ subName subEntity,
      (subName, subEntity) ∈ subImport ↔
      subEntity ∈ owns entity ∧
      (subName, subEntity) ∈ exportRel) →
    inscopeRel = { (name, entity) } ∪ subImport →
    ---------------------------------------------------------------------------
    ImportItemJ exportRel (ImportItem.All name) inscopeRel

  | Some :
    ∀ exportRel name names entity subImport inscopeRel,
    (name, entity) ∈ exportRel →
    (∀ subName subEntity,
      (subName, subEntity) ∈ subImport ↔
      subEntity ∈ owns entity ∧
      subName ∈ names ∧
      (subName, subEntity) ∈ exportRel) →
    inscopeRel = { (name, entity) } ∪ subImport →
    ---------------------------------------------------------------------------
    ImportItemJ exportRel (ImportItem.Some name names) inscopeRel

def toQualifiedInscope (qual : Bool) (asname : ModName) (rel : UnqInscopeRel) : InscopeRel :=
  if qual
  then rel.mapDom (mkQual asname)
  else rel.mapDom (mkQual asname) ∪ rel.mapDom mkUnqual

/-- Specify the semantics of a single import statement -/
inductive ImportJ : ExportEnv → Import → InscopeRel → Prop where
  | Hiding :
    ∀ qual modname asname items exportRel hiddenInscopeRels,
    exports[modname]? = some exportRel →
    Forall2
      (λ importItem inscopeRel => ImportItemJ exportRel importItem inscopeRel)
      items hiddenInscopeRels →
    inscopeRel = toQualifiedInscope qual asname (exportRel \ (FinRel.unions hiddenInscopeRels)) →
    ---------------------------------------------------------------------------
    ImportJ exports (Import.mk qual modname asname true items) inscopeRel

  | Exposing :
    ∀ qual modname asname items exportRel inscopeRels,
    exports[modname]? = some exportRel →
    Forall2
      (λ importItem inscopeRel => ImportItemJ exportRel importItem inscopeRel)
      items inscopeRels →
    inscopeRel = toQualifiedInscope qual asname (FinRel.unions inscopeRels) →
    ---------------------------------------------------------------------------
    ImportJ exports (Import.mk qual modname asname false items) inscopeRel

/-
Semantic of Exports
-/

/-- Export relation for a type/function, without constructors or fields -/
def ExportRootJ (inscope : InscopeRel) (name : QName) (exportRel : ExportRel) : Prop :=
  (∀ expName entity,
    (expName, entity) ∈ exportRel ↔
    expName = getQualified name ∧
    not (isCon entity) ∧
    (name, entity) ∈ inscope)

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
      (expName, entity) ∈ subExport ↔
      expName = getQualified subName ∧
      (∃ ownEntity,
        ownEntity ∈ rootExport.rng ∧
        entity ∈ owns ownEntity) ∧
      (subName, entity) ∈ inscope) →
    exportRel = rootExport ∪ subExport →
    --------------------------------------------------
    ExportItemJ inscope (ExportItem.All name) exportRel

  | Some :
    ∀ inscope name names rootExport subExport,
    -- Same structure as above
    ExportRootJ inscope name rootExport →
    (∀ expName entity subName,
      (expName, entity) ∈ subExport ↔
      expName = getQualified subName ∧
      (∃ ownEntity,
        ownEntity ∈ rootExport.rng ∧
        entity ∈ owns ownEntity) ∧
      (subName, entity) ∈ inscope ∧
      expName ∈ names /- Only difference from [All] -/) →
    exportRel = rootExport ∪ subExport →
    --------------------------------------------------
    ExportItemJ inscope (ExportItem.Some name names) _

  | Module :
    ∀ inscope modname exportRel,
    (∀ name entity,
      (name, entity) ∈ exportRel ↔
      (QName.Qualified modname name, entity) ∈ inscope ∧
      (QName.UnQualified name, entity) ∈ inscope) →
    -------------------------------------------------
    ExportItemJ inscope (ExportItem.Module modname) exportRel

def export_item (inscope : InscopeRel)(exp_item : ExportItem) : ExportRel :=
  match exp_item with
  | ExportItem.Single name =>
      Finset.image (RelEntry.mk (getQualified name)) (inscope.apply name)
  | ExportItem.All name =>
      let nameEntities := inscope.apply name;
      let ownedEntities := nameEntities.unionMap owns
      FinRel.mapDom getQualified
        ( /- All the root entities -/
          (inscope.restrictDom (.== name)) ∪
          /- All the owned entities of the root -/
          (inscope.restrictRng (λ entity => entity ∈ ownedEntities))
        )
  | ExportItem.Some name names =>
      let nameEntities := inscope.apply name;
      let ownedEntities := nameEntities.unionMap owns
      FinRel.mapDom getQualified
        ( /- All the root entities -/
          (inscope.restrictDom (.== name)) ∪
          /- All the owned entities of the root matching the [names] -/
          (inscope.restrictDomRng
            (λ n => List.elem (getQualified n) names)
            (λ entity => entity ∈ ownedEntities))
        )
  | ExportItem.Module modName =>
    /- All the entities qualified by modName -/
    let qualEntities := inscope.restrictDom (λ n => getQualifier n == some modName);
    /- All the unqualified names -/
    let unqualEntities := inscope.restrictDom (λ n => getQualifier n == none);
    (qualEntities.mapDom getQualified) ∩
    (unqualEntities.mapDom getQualified)

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
    exportRel = FinRel.unions exportRels →
    ----------------------------------------------------------
    ExportsJ m inscope (ExportList.Explicit exports) exportRel

def exports (mod : Module)(inscope : InscopeRel)(exp_list : ExportList) : ExportRel :=
  sorry

theorem exports_correct :
  exports mod inscope exp_list = export_rel →
  ExportsJ mod inscope exp_list export_rel :=
  sorry

-- TODO
def mEntSpec : sorry := sorry

-- TODO find a better name
def mImp (expsOf : ModName -> FinRel Name Entity) (imp : Import): FinRel QName Entity :=
  if Import.qualified imp then
    qs
  else
    sorry
  where
    qs := incoming.mapDom (mkQual (Import.as imp))
    unqs := incoming.mapDom mkUnqual
    listed := FinRel.unions $ List.map (sorry isHiding exps) (Import.items imp)
    incoming :=
      if isHiding then
        exps \ listed
      else
        listed
    isHiding := Import.hiding_ imp
    exps := expsOf (Import.source imp)

def inscope (m : Module) (expsOf : ModName → FinRel Name Entity) : InscopeRel :=
  imports ∪ locals
  where
    defEnts := Module.defines m
    locals := defEnts.mapDom mkUnqual ∪
              defEnts.mapDom (mkQual (Module.name m))
    imports := FinRel.unions $ List.map (mImp expsOf) (Module.imports m)
