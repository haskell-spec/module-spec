-- This module defines `Entities`, i.e. things that can be imported or exported.
import ModuleSpec.Relations

structure EntityFun where
  name : String
  deriving Ord, BEq

structure EntityTmCon where
  name : String
  deriving Ord, BEq

structure EntityFieldLabel where
  name : String
  deriving Ord, BEq

structure EntityTyCon where
  name : String
  tmcons : List EntityTmCon
  fieldlabels : List EntityFieldLabel
  deriving Ord, BEq

structure EntityClassMethod where
  name : String
  deriving Ord, BEq

structure EntityTyClass where
  name : String
  methods : List EntityClassMethod
  deriving Ord, BEq

inductive Entity : Type where
    /-- A function -/
  | Fun : EntityFun → Entity
    /-- A type constructor -/
  | TyCon : EntityTyCon → Entity
    /-- A term constructor -/
  | TmCon : EntityTmCon → Entity
    /-- The field label of a record -/
  | FieldLabel : EntityFieldLabel → Entity
    /-- A typeclass -/
  | TyClass : EntityTyClass → Entity
    /-- A typeclass method -/
  | ClassMethod : EntityClassMethod → Entity
  deriving Ord, BEq

def isCon (e : Entity) : Bool :=
  match e with
  | Entity.TmCon _ => true
  | _ => false

/-- Things that can be converted to an `Entity` -/
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
  toEntity x := Entity.TyClass x

instance ToEntityClsMethod : ToEntity EntityClassMethod where
  toEntity x := Entity.ClassMethod x

def owns (e : Entity) : Set Entity :=
  match e with
  | Entity.Fun _ => Std.TreeSet.empty
  | Entity.TyCon ⟨_,tmcons,fieldlabels⟩ => Std.TreeSet.ofList (tmcons.map ToEntity.toEntity  ++ fieldlabels.map ToEntity.toEntity)
  | Entity.TmCon _ => Std.TreeSet.empty
  | Entity.FieldLabel _ => Std.TreeSet.empty
  | Entity.TyClass ⟨_,clsmethods⟩ => Std.TreeSet.ofList (clsmethods.map ToEntity.toEntity)
  | Entity.ClassMethod _ => Std.TreeSet.empty
