-- Section 2: Relations

import Std.Data.TreeSet

abbrev Set (α : Type)[Ord α] := Std.TreeSet α

structure RelEntry (α β : Type) : Type where
  dom : α
  rng : β

instance OrdRelEntry {α β : Type}[Ord α][Ord β] : Ord (RelEntry α β) where
  compare x y :=
  match compare x.dom y.dom with
    | Ordering.lt => Ordering.lt
    | Ordering.gt => Ordering.gt
    | Ordering.eq => compare x.rng y.rng

abbrev Rel (α β : Type)[Ord α][Ord β] : Type :=
  Std.TreeSet (RelEntry α β)

def emptyRel {α β : Type}[Ord α][Ord β] : Rel α β :=
  Std.TreeSet.empty

def listToRel {α β : Type} [Ord α] [Ord β]
              (xs : List (RelEntry α β)) : Rel α β :=
  Std.TreeSet.ofList xs

def relToList {α β : Type} [Ord α] [Ord β]
              (r : Rel α β) : List (RelEntry α β) :=
  Std.TreeSet.toList r

def restrictDom {α β : Type} [Ord α] [Ord β]
                (f : α → Bool) (r : Rel α β) : Rel α β :=
  let g (x : RelEntry α β) : Bool := f x.dom
  Std.TreeSet.filter g r

def restrictRng {α β : Type} [Ord α] [Ord β]
                (f : β → Bool) (r : Rel α β) : Rel α β :=
  let g (x : RelEntry α β) : Bool := f x.rng
  Std.TreeSet.filter g r

def dom {α β : Type} [Ord α][Ord β] (r : Rel α β) : Set α :=
  Std.TreeSet.ofList ((Std.TreeSet.toList r).map (λ x => x.dom))

def rng {α β : Type} [Ord α][Ord β] (r : Rel α β) : Set β :=
  Std.TreeSet.ofList ((Std.TreeSet.toList r).map (λ x => x.rng))

def mapDom {α β γ : Type} [Ord α][Ord β][Ord γ]
           (f : α → γ)(r : Rel α β) : Rel γ β :=
  sorry

def mapRng {α β γ : Type} [Ord α][Ord β][Ord γ]
           (f : β → γ)(r : Rel α β) : Rel α γ :=
  sorry

def intersectRel {α β : Type}[Ord α][Ord β]
                 (r₁ r₂ : Rel α β) : Rel α β :=
  sorry

def unionRels {α β : Type} [Ord α] [Ord β]
              (xs : List (Rel α β)) : Rel α β :=
  sorry

def minusRel {α β : Type} [Ord α][Ord β]
             (r₁ r₂ : Rel α β) : Rel α β :=
  sorry

def partitionDom {α β : Type} [Ord α] [Ord β]
                 (f : α → Bool)(r : Rel α β) : (Rel α β × Rel α β) :=
  ⟨restrictDom f r, restrictDom (not ∘ f) r⟩

def applyRel {α β : Type} [BEq α][Ord α] [Ord β]
             (r : Rel α β) (x : α) : List β :=
  Std.TreeSet.toList (rng (restrictDom (λ y => BEq.beq y x) r))

def unionMapSet {α β : Type}[Ord α][Ord β]
                (f : α → Set β)(s : Set α) : Set β :=
  sorry

-- Section 3: Names and Entities

inductive Entity : Type where
  deriving Ord

def isCon : Entity → Bool := sorry

def owns : Entity → Set Entity := sorry

inductive Name where
  | MkName : String → Name
  deriving Ord

inductive ModName where
  | ModName : String → ModName
  deriving Ord

inductive QName where
  | Qualified : ModName → Name → QName
  | UnQualified : Name → QName
  deriving Ord


def getQualifier (q : QName) : Option ModName :=
  match q with
  | QName.Qualified m _ => some m
  | QName.UnQualified _ => none

def getQualified(q : QName) : Name :=
  match q with
  | QName.Qualified _ n => n
  | QName.UnQualified n => n

def mkUnqual(n : Name) : QName :=
  QName.UnQualified n

def mkQual(m : ModName)(n : Name) : QName :=
  QName.Qualified m n

def isQual(q : QName) : Bool :=
  match q with
  | QName.Qualified _ _ => true
  | QName.UnQualified _ => false

def qual(m : ModName)(q : QName) : QName :=
  mkQual m (getQualified q)

class ToSimple (α : Type) where
  toSimple : α → Name

instance ToSimpleName : ToSimple Name where
  toSimple x := x

instance ToSimpleQName : ToSimple QName where
  toSimple x := getQualified x

-- Section 4: Abstract Syntax

inductive SubSpec where
  | AllSubs : SubSpec
  | Subs : List Name → SubSpec

inductive EntSpec (j : Type) where
  | Ent : j → Option SubSpec → EntSpec j

inductive ExpListEntry where
  | EntExp : EntSpec QName → ExpListEntry
  | ModuleExp : ModName → ExpListEntry

structure Import where
  impQualified : Bool
  impSource : ModName
  impAs : ModName
  impHiding : Bool
  impList : List (EntSpec Name)

structure Module where
  modName : ModName
  modExpList : Option (List ExpListEntry)
  modImport : List Import
  modDefines : Rel Name Entity

-- Section 5 : The semantics of Imports and Exports

def mEntSpec {j : Type} [Ord j] [ToSimple j] :
  Bool → Rel j Entity → EntSpec j → Rel j Entity := sorry

def mExpListEntry (inscp : Rel QName Entity)
                  (entry : ExpListEntry) : Rel QName Entity :=
  match entry with
  | ExpListEntry.EntExp it => mEntSpec false inscp it
  | ExpListEntry.ModuleExp m =>
    let ⟨qs,unqs⟩ := partitionDom isQual inscp
    intersectRel (mapDom (qual m) unqs) qs

def exports (mod : Module)
            (inscp : Rel QName Entity) : Rel Name Entity :=
  match mod.modExpList with
  | none => mod.modDefines
  | some es =>
    let exps := List.map (mExpListEntry inscp) es
    mapDom getQualified (unionRels exps)


def mImp : (ModName → Rel Name Entity) → Import → Rel QName Entity := sorry

def inscope : Module → (ModName → Rel Name Entity) → Rel QName Entity := sorry

-- Section 6: Error Detection

inductive ModSysErr where
  | UndefinedModuleAlias : ModName → ModSysErr
  | UndefinedExport : QName → ModSysErr
  | UndefinedSubExport : QName → Name → ModSysErr
  | AmbiguousExport : Name → List Entity → ModSysErr
  | MissingModule : ModName → ModSysErr
  | UndefinedImport : ModName → Name → ModSysErr
  | UndefinedSubImport : ModName → Name → Name → ModSysErr

def chkAmbigExps : Rel Name Entity → List ModSysErr :=
  sorry

def chkEntSpec {j : Type} [Ord j] [ToSimple j] :
  Bool → (j → ModSysErr) → (j → Name → ModSysErr) → EntSpec j
 → Rel j Entity → List ModSysErr := sorry

def chkExpSpec : Rel QName Entity → Module → List ModSysErr := sorry

def chkImport : Rel Name Entity → Import → List ModSysErr := sorry

def chkModule : (ModName → Option (Rel Name Entity)) → Rel QName Entity → Module → List ModSysErr := sorry
