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
