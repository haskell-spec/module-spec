-- Section 2: Relations

import Std.Data.TreeSet

abbrev Set (α : Type)[Ord α] := Std.TreeSet α

def SetMap {α β : Type}[Ord α][Ord β]
           (f : α → β)(s : Set α) : Set β :=
           Std.TreeSet.ofList ((Std.TreeSet.toList s).map f)

def concatMap {α β : Type}
    (f : α → List β)(xs : List α) : List β := List.flatMap f xs

def partition {α : Type} (f : α → Bool) (xs : List α) : (List α × List α) :=
  ⟨ xs.filter f, xs.filter (not ∘ f) ⟩

structure RelEntry (α β : Type) : Type where
  dom : α
  rng : β
  deriving Repr

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
  listToRel ((relToList r).map (λ ⟨x,y⟩ => ⟨f x, y⟩))


def mapRng {α β γ : Type} [Ord α][Ord β][Ord γ]
           (f : β → γ)(r : Rel α β) : Rel α γ :=
  listToRel ((relToList r).map (λ ⟨x,y⟩ => ⟨x, f y⟩))

def intersectRel {α β : Type}[Ord α][Ord β]
                 (r₁ r₂ : Rel α β) : Rel α β :=
  Inter.inter r₁ r₂

def unionRels {α β : Type} [Ord α] [Ord β]
              (xs : List (Rel α β)) : Rel α β :=
  xs.foldl Std.TreeSet.union emptyRel

def minusRel {α β : Type} [Ord α][Ord β]
             (r₁ r₂ : Rel α β) : Rel α β :=
  SDiff.sdiff r₁ r₂

def partitionDom {α β : Type} [Ord α] [Ord β]
                 (f : α → Bool)(r : Rel α β) : (Rel α β × Rel α β) :=
  ⟨restrictDom f r, restrictDom (not ∘ f) r⟩

def applyRel {α β : Type} [BEq α][Ord α] [Ord β]
             (r : Rel α β) (x : α) : List β :=
  Std.TreeSet.toList (rng (restrictDom (λ y => BEq.beq y x) r))

def unionMapSet {α β : Type}[Ord α][Ord β]
                (f : α → Set β)(s : Set α) : Set β :=
  let xs := Std.TreeSet.toList s
  let ys := xs.map f
  ys.foldl Std.TreeSet.union Std.TreeSet.empty

def example1 : Rel String String :=
  listToRel [⟨"a", "b"⟩,⟨"c", "d"⟩,⟨"a", "x"⟩]

def example2 : Rel String String :=
  listToRel [⟨"a", "b"⟩,⟨"e", "f"⟩]

#eval relToList (unionRels [example1, example2])
#eval relToList (intersectRel example1 example2)
#eval relToList (minusRel example1 example2)
#eval applyRel example1 "a"

-- Section 3: Names and Entities

structure EntityFun where
  name : String
  deriving Ord

structure EntityTmCon where
  name : String
  deriving Ord

structure EntityFieldLabel where
  name : String
  deriving Ord

structure EntityTyCon where
  name : String
  tmcons : List EntityTmCon
  fieldlabels : List EntityFieldLabel
  deriving Ord

structure EntityClassMethod where
  name : String
  deriving Ord

structure EntityTyClass where
  name : String
  methods : List EntityClassMethod
  deriving Ord

inductive Entity : Type where
  | Fun : EntityFun → Entity
  | TyCon : EntityTyCon → Entity
  | TmCon : EntityTmCon → Entity
  | FieldLabel : EntityFieldLabel → Entity
  | TyCls : EntityTyClass → Entity
  | ClsMethod : EntityClassMethod → Entity
  deriving Ord

def isCon (e : Entity) : Bool :=
  match e with
  | Entity.TmCon _ => true
  | _ => false

class ToEntity (α : Type) where
  toEntity : α → Entity

instance ToEntityFun : ToEntity EntityFun where
  toEntity x := Entity.Fun x

instance ToEntityTyCon : ToEntity EntityTyCon where
  toEntity x := Entity.TyCon x

instance ToEntityTmCon : ToEntity EntityTmCon where
  toEntity x := Entity.TmCon x

instance ToEntityFieldLabel : ToEntity EntityFieldLabel where
  toEntity x := Entity.FieldLabel x

instance ToEntityTyCls : ToEntity EntityTyClass where
  toEntity x := Entity.TyCls x

instance ToEntityClsMethod : ToEntity EntityClassMethod where
  toEntity x := Entity.ClsMethod x

def owns (e : Entity) : Set Entity :=
  match e with
  | Entity.Fun _ => Std.TreeSet.empty
  | Entity.TyCon ⟨_,tmcons,fieldlabels⟩ => Std.TreeSet.ofList (tmcons.map ToEntity.toEntity  ++ fieldlabels.map ToEntity.toEntity)
  | Entity.TmCon _ => Std.TreeSet.empty
  | Entity.FieldLabel _ => Std.TreeSet.empty
  | Entity.TyCls ⟨_,clsmethods⟩ => Std.TreeSet.ofList (clsmethods.map ToEntity.toEntity)
  | Entity.ClsMethod _ => Std.TreeSet.empty

inductive Name where
  | MkName : String → Name
  deriving Ord, BEq

inductive ModName where
  | ModName : String → ModName
  deriving Ord, BEq

inductive QName where
  | Qualified : ModName → Name → QName
  | UnQualified : Name → QName
  deriving Ord, BEq


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

def mEntSpec {j : Type} [Ord j] [BEq j] [ToSimple j]
             (isHiding : Bool)
             (rel : Rel j Entity)
             (e : EntSpec j) : Rel j Entity :=
    let ⟨x, subspec⟩ := e
    let consider :=
      if isHiding && subspec.isNone
        then λ _ => true
        else not ∘ isCon
    let mSpec := restrictRng consider (restrictDom (λ y => y == x) rel)
    let allSubs := unionMapSet owns (rng mSpec)
    let subs := restrictRng (λ x => x ∈ allSubs) rel
    let mSub :=
      match subspec with
      | none => emptyRel
      | some SubSpec.AllSubs => subs
      | some (SubSpec.Subs xs) =>
        restrictDom ((λ y => xs.contains y) ∘ ToSimple.toSimple) subs
    unionRels [mSpec, mSub]


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


def mImp (expsOf : ModName → Rel Name Entity)(imp : Import) : Rel QName Entity :=
  let isHiding := imp.impHiding
  let exps := expsOf imp.impSource
  let listed := unionRels (imp.impList.map (mEntSpec isHiding exps))
  let incoming :=
    if isHiding
      then minusRel exps listed
      else listed
  let qs := mapDom (mkQual imp.impAs) incoming
  let unqs := mapDom mkUnqual incoming
  if imp.impQualified
    then qs
    else unionRels [unqs, qs]

def inscope (m : Module)(expsOf : ModName → Rel Name Entity) : Rel QName Entity :=
  let defEnts := m.modDefines
  let locals := unionRels [mapDom mkUnqual defEnts, mapDom (mkQual m.modName) defEnts]
  let imports := unionRels (m.modImport.map (mImp expsOf))
  unionRels [imports, locals]

-- Section 6: Error Detection

inductive ModSysErr where
  | UndefinedModuleAlias : ModName → ModSysErr
  | UndefinedExport : QName → ModSysErr
  | UndefinedSubExport : QName → Name → ModSysErr
  | AmbiguousExport : Name → List Entity → ModSysErr
  | MissingModule : ModName → ModSysErr
  | UndefinedImport : ModName → Name → ModSysErr
  | UndefinedSubImport : ModName → Name → Name → ModSysErr

def chkAmbigExps (exps: Rel Name Entity) : List ModSysErr :=
  let ambig n ents :=
    match ents with
    | (_ :: _ :: _) => [ModSysErr.AmbiguousExport n ents]
    | _ => []
  let isAmbig n :=
    let (cons, other) := partition isCon (applyRel exps n)
    ambig n cons ++ ambig n other
  concatMap isAmbig (Std.TreeSet.toList (dom exps))

def chkEntSpec {j : Type} [Ord j][BEq j][ToSimple j]
               (isHiding : Bool)
               (errUndef : j → ModSysErr)
               (errUndefSub : j → Name → ModSysErr)
               (e : EntSpec j)
               (rel : Rel j Entity) : List ModSysErr :=
  let ⟨x, subspec⟩ := e
  let consider :=
    if isHiding && subspec.isNone
      then λ _ => true
      else not ∘ isCon
  let xents := (applyRel rel x).filter consider
  let chk := λ ent =>
    match subspec with
    | some (SubSpec.Subs subs) =>
      let subsInScope : Set Name := SetMap ToSimple.toSimple (dom (restrictRng (λ y => (owns ent).contains y) rel))
      (subs.filter (not ∘ (λ y => subsInScope.contains y))).map (errUndefSub x)
    | _ => []
  match xents with
  | [] => [errUndef x]
  | ents => concatMap chk ents


def chkExpSpec (inscp : Rel QName Entity)(mod : Module) : List ModSysErr :=
  let aliases := mod.modName :: (mod.modImport.map (λ x => x.impAs))
  let chk (e : ExpListEntry) : List ModSysErr :=
    match e with
    | ExpListEntry.ModuleExp x =>
      if aliases.contains x
        then []
        else [ModSysErr.UndefinedModuleAlias x]
    | ExpListEntry.EntExp spec =>
      chkEntSpec false ModSysErr.UndefinedExport ModSysErr.UndefinedSubExport spec inscp
  match mod.modExpList with
  | none => []
  | some exps => concatMap chk exps

def chkImport (exps: Rel Name Entity) (imp : Import) : List ModSysErr :=
  let src := imp.impSource
  let chk spec :=
    chkEntSpec imp.impHiding (ModSysErr.UndefinedImport src) (ModSysErr.UndefinedSubImport src) spec exps
  concatMap chk imp.impList


def chkModule (expsOf : ModName → Option (Rel Name Entity))
              (inscp: Rel QName Entity)
              (mod : Module) : List ModSysErr :=
  let mod_exports :=
    match expsOf mod.modName with
    | none => emptyRel
    | some mod_exports => mod_exports
  let impSources := mod.modImport.map (λ imp => (imp, expsOf (imp.impSource)))
  let missingModules : List ModName :=
    List.eraseDups ((impSources.filter (λ x => x.snd.isNone)).map (λ y => y.fst.impSource))
  let missingModuleErrs :=
    if missingModules.isEmpty
      then
        let somes := impSources.filterMap (λ x => match x.snd with
                                                | none => none
                                                | some exps => some (x.fst, exps))
        let errs := concatMap (λ x => chkImport x.snd x.fst) somes
        chkExpSpec inscp mod ++ errs
      else missingModules.map ModSysErr.MissingModule
  chkAmbigExps mod_exports ++ missingModuleErrs
