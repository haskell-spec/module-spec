inductive SubSpec where
  | AllSubs
  | Subs (l : List Name)

structure EntSpec (j : Type) where
  item : j
  sub : Option SubSpec
