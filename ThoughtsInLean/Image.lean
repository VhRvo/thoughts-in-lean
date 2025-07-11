inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

#print inverse

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a

def inverse'' {f : α → β} : (b : β) → ImageOf f b → α :=
  fun b imgOf =>
    match imgOf with
    | imf a => a
