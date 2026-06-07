-- Syntax of Export Lists

import ModuleSpec.Names

/--
Describes the individual items specified in an export list:
```text
module A (...)
          ^^^
           \-- ExportItems
```
-/
inductive ExportItem where
    /-- An `ExportItem` of the form `f` -/
  | Single : QName → ExportItem
    /-- An `ExportItem` of the form `f(..)` -/
  | All : QName → ExportItem
    /-- An `ExportItem` of the form `f(f₁,…,fₙ)` -/
  | Some : QName → List Name → ExportItem
    /-- An `ExportItem` of the form `module A` -/
  | Module : ModName → ExportItem

inductive ExportList where
  | Implicit
  | Explicit : List ExportItem → ExportList
