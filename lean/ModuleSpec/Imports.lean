import ModuleSpec.Names

/--
Describes the individual items specified in an import statement:
```text
import A (...)
          ^^^
           \-- ImportItems
```
-/
inductive ImportItem where
    /-- An `ImportItem` of the form `f` -/
  | Single : Name → ImportItem
    /-- An `ImportItem` of the form `f(..)` -/
  | All : Name → ImportItem
    /-- An `ImportItem` of the form `f(f₁,…,fₙ)` -/
  | Some : Name → List Name → ImportItem


structure Import where
  qualified : Bool
  source : ModName
  as : ModName
  hiding_ : Bool
  items : List ImportItem
