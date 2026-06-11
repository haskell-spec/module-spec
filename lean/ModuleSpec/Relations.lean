import Mathlib.Data.Rel
import Mathlib.Data.Finite.Set
import Mathlib.Data.Finset.Sort
import Mathlib.Data.PFun
import Mathlib.Data.Prod.Lex
import Mathlib.Data.String.Basic

def concatMap {α β : Type}
    (f : α → List β)(xs : List α) : List β := List.flatMap f xs

def partition {α : Type} (f : α → Bool) (xs : List α) : (List α × List α) :=
  ⟨ xs.filter f, xs.filter (not ∘ f) ⟩

/-
#print Decidable

class Relatable α extends Ord α where
  decEq : DecidableEq α

instance { x: Relatable α } : DecidableEq α := x.decEq

instance [Ord α][DecidableEq α] : Relatable α :=
  by
    constructor
    assumption
-/

abbrev RelEntry α β := Lex (α × β)

namespace RelEntry

def mk (a : α) (b : β) : RelEntry α β := (a, b)

end RelEntry

abbrev FinRel (α β : Type) : Type :=
  Finset (RelEntry α β)

namespace Finset

def fromList  [DecidableEq α] (xs : List α) : Finset α :=
  List.toFinset xs

def unionMap {α β : Type}[DecidableEq α][DecidableEq β]
                (s : Finset α) (f : α → Finset β) : Finset β :=
  s.fold Union.union ∅ f

end Finset

namespace FinRel

def empty {α β : Type} : FinRel α β := ∅

def fromList {α β : Type} [DecidableEq α][DecidableEq β]
              (xs : List (RelEntry α β)) : FinRel α β :=
  List.toFinset xs

def restrictDom {α β : Type}
                (f : α → Bool) (r : FinRel α β) : FinRel α β :=
  let g (x : RelEntry α β) : Prop := f x.fst
  Finset.filter g r

def restrictRng {α β : Type}
                (f : β → Bool) (r : FinRel α β) : FinRel α β :=
  let g (x : RelEntry α β) : Prop := f x.snd
  Finset.filter g r

def restrictDomRng {α β: Type}
              (f : α → Bool)(g: β → Bool): FinRel α β → FinRel α β :=
  restrictRng g ∘ restrictDom f

def dom {α β : Type} [DecidableEq α] (r : FinRel α β) : Finset α :=
  Finset.image Prod.fst r

def rng {α β : Type} [DecidableEq β] (r : FinRel α β) : Finset β :=
  Finset.image Prod.snd r

def mapDom {α β γ : Type}[DecidableEq β][DecidableEq γ]
           (f : α → γ)(r : FinRel α β) : FinRel γ β :=
  Finset.image (Prod.map f id) r

def mapRng {α β γ : Type}[DecidableEq α][DecidableEq γ]
           (f : β → γ)(r : FinRel α β) : FinRel α γ :=
  Finset.image (Prod.map id f) r

def mapDomRng {α β γ δ : Type}[DecidableEq γ][DecidableEq δ]
              (f : α → γ)(g: β → δ): FinRel α β → FinRel γ δ :=
  Finset.image (Prod.map f g)

def intersect {α β : Type}[DecidableEq α][DecidableEq β]
                 (r₁ r₂ : FinRel α β) : FinRel α β :=
  r₁ ∩ r₂

def unions {α β : Type} [DecidableEq α][DecidableEq β]
              (xs : List (FinRel α β)) : FinRel α β :=
  xs.foldl Union.union ∅

def minus {α β : Type} [DecidableEq α][DecidableEq β]
             (r₁ r₂ : FinRel α β) : FinRel α β :=
  r₁ \ r₂

def partitionDom {α β : Type} [Ord α] [Ord β]
                 (f : α → Bool)(r : FinRel α β) : (FinRel α β × FinRel α β) :=
  ⟨restrictDom f r, restrictDom (not ∘ f) r⟩

def apply {α β : Type} [DecidableEq α][DecidableEq β]
             (r : FinRel α β) (x : α) : Finset β :=
  rng $ restrictDom (λ y => x == y) $ r

end FinRel

def example1 : FinRel String String :=
  { ⟨"a", "b"⟩,⟨"c", "d"⟩,⟨"a", "x"⟩ }

def example2 : FinRel String String :=
  Finset.fromList [⟨"a", "b"⟩,⟨"e", "f"⟩]

#eval (FinRel.unions [example1, example2])
#eval (FinRel.intersect example1 example2)
#eval (FinRel.minus example1 example2)
#eval FinRel.apply example1 "a"

/- Or alternatively -/
#eval (example1 ∪ example2)
#eval (example1 ∩ example2)
#eval (example1 \ example2)
