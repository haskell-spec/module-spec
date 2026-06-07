inductive Forall2 {α β : Type}(P : α → β → Prop) : List α → List β → Prop where
  | Nil : Forall2 P [] []
  | Cons : Forall2 P xs ys →
           P x y →
           Forall2 P (x :: xs) (y :: ys)
