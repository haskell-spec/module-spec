import ModuleSpec.Modules

/- An export relation is unambiguous if it doesn't export a name
   collision for names in the same namespace. Note that constructors
   live in a different namespace to all other names. -/
def UnambiguousJ (exportRel : ExportRel) : Prop :=
  ∀ name entity1 entity2,
    RelEntry.mk name entity1 ∈ exportRel →
    RelEntry.mk name entity2 ∈ exportRel →
    entity1 = entity2 ∨
    isCon entity1 ≠ isCon entity2

def localScope (m : Module) : InscopeRel :=
  mapDom mkUnqual (m.defines)

inductive WfModuleJ (exports : ExportEnv) (m : Module) : Prop where
  | WfModule : ∀ importRels,
      /- TODO: both the [ImportJ] and [ExportJ] judgments check
         well-scoping, so we can avoid re-checking them here. -/
      Forall2 (λ (imp : Import) (inscopeRel : InscopeRel) =>
        ImportJ exports imp inscopeRel) m.imports importRels →
      ExportsJ m
        (unionRels (List.cons (localScope m) importRels))
        (m.exports) exportRel →
      UnambiguousJ exportRel →
      ----------------------------------
      WfModuleJ exports m
