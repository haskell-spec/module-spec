import ModuleSpec.Relations

inductive Name where
  | MkName : String → Name
  deriving Ord, BEq, ReflBEq, LawfulBEq, Hashable, DecidableEq

inductive ModName where
  | ModName : String → ModName
  deriving Ord, BEq, ReflBEq, LawfulBEq, Hashable, DecidableEq

inductive QName where
  | Qualified : ModName → Name → QName
  | UnQualified : Name → QName
  deriving Ord, BEq, ReflBEq, LawfulBEq, Hashable, DecidableEq

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
