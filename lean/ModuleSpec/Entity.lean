-- This module defines `Entities`, i.e. things that can be imported or exported.
import ModuleSpec.Relations
import Mathlib.Data.String.Basic

structure EntityFun where
  name : String
  deriving Ord, BEq, ReflBEq, LawfulBEq, DecidableEq

structure EntityTmCon where
  name : String
  deriving Ord, BEq, ReflBEq, LawfulBEq, DecidableEq

structure EntityFieldLabel where
  name : String
  deriving Ord, BEq, ReflBEq, LawfulBEq, DecidableEq

structure EntityTyCon where
  name : String
  tmcons : List EntityTmCon
  fieldlabels : List EntityFieldLabel
  deriving Ord, BEq, ReflBEq, LawfulBEq, DecidableEq

structure EntityClassMethod where
  name : String
  deriving Ord, BEq, ReflBEq, LawfulBEq, DecidableEq

structure EntityTyClass where
  name : String
  methods : List EntityClassMethod
  deriving Ord, BEq, ReflBEq, LawfulBEq, DecidableEq

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
  deriving Ord, BEq, ReflBEq, LawfulBEq, DecidableEq

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

def owns (e : Entity) : Finset Entity :=
  match e with
  | Entity.Fun _ => ∅
  | Entity.TyCon ⟨_,tmcons,fieldlabels⟩ => Finset.fromList (tmcons.map ToEntity.toEntity  ++ fieldlabels.map ToEntity.toEntity)
  | Entity.TmCon _ => ∅
  | Entity.FieldLabel _ => ∅
  | Entity.TyClass ⟨_,clsmethods⟩ => Finset.fromList (clsmethods.map ToEntity.toEntity)
  | Entity.ClassMethod _ => ∅
