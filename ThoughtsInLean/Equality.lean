
#print Eq

set_option pp.proofs true
-- set_option inductive.autoPromoteIndices false

def subst {α} {a b : α} (motive : α → Sort u) (h : a = b) (p : motive a) : motive b :=
  match b, h with
  | .(a), Eq.refl a => p

def subst₁ {α β} {a b : α} (f : α → β) (h : a = b) : f a = f b :=
  match b, h with
  | .(a), Eq.refl a => Eq.refl (f a)

def subst₂ {α β γ} {a₁ a₂ : α} {b₁ b₂ : β} (f : α → β → γ) (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) : f a₁ b₂ = f a₂ b₂ :=
  match a₂, h₁ with
  | .(a₁), Eq.refl a₁ =>
    match b₂, h₂ with
    | .(b₁), Eq.refl b₁ =>
      Eq.refl (f a₁ b₁)

def subst₃ {α β} {f₁ f₂ : α → β} {a : α} (h : f₁ = f₂) : f₁ a = f₂ a :=
  match f₂, h with
  | .(f₁), Eq.refl f₁ =>
    Eq.refl (f₁ a)

def symm (h : a = b) : b = a :=
  match b, h with
  | .(a), Eq.refl a => Eq.refl a

def symm₁ (h : a = b) : b = a :=
  match a, h with
  | .(b), Eq.refl b => Eq.refl b

def symm' {a b : α} (h : a = b) : b = a :=
  @Eq.rec α a (motive := fun x _ => x = a) (Eq.refl a) b h


def symm₁' {a b : α} (h : a = b) : b = a :=
  @Eq.rec α b (motive := fun x _ => b = x) (Eq.refl b) a h.symm

def symm₂' {a b : α} (h : a = b) : b = a :=
  @Eq.rec α b (motive := fun x _ => b = x) (Eq.refl b) a h.symm

def symm.under.{u_1} : ∀ {α : Sort u_1} {A B : α}, A = B → B = A :=
  fun {α} {A B} h =>
    match B, h with
    | .(A), Eq.refl A => Eq.refl A

#print symm.under

def symm.under1.{u_1} : ∀ {α : Sort u_1} {A B : α}, A = B → B = A :=
  fun {α} {A B} h =>
    match A, h with
    | .(B), Eq.refl B => Eq.refl B

theorem symm.tactic (h : A = B) : B = A := by
  cases h with
  | refl => exact Eq.refl A

#print symm.tactic

namespace My

inductive MEq {A : Type} (x : A) : A → Prop where
| myrefl : MEq x x

def symm (a b : A) (h : MEq a b) : MEq b a :=
  match h with
  | @MEq.myrefl A a => MEq.myrefl

inductive MEq1 {A : Type} : A → A → Prop where
| myrefl x : MEq1 x x

#print MEq.rec
-- recursor My.MEq.rec.{u} : {A : Type} → {x : A} → {motive : (a : A) → MEq x a → Sort u} → motive x MEq.myrefl → {a : A} → (t : MEq x a) → motive a t
#print MEq1.rec
-- recursor My.MEq1.rec.{u} : {A : Type} → {a : A} → {motive : (a_1 : A) → MEq1 a a_1 → Sort u} → motive a (MEq1.myrefl a) → {a_1 : A} → (t : MEq1 a a_1) → motive a_1 t

theorem symm0 (a b c : A) (h1 : MEq1 b c) (h : MEq1 a b) : MEq1 b a :=
  match h with
  | MEq1.myrefl a => by
    exact MEq1.myrefl a

theorem symm1 (a b c : A) (h1 : MEq1 b c) (h : MEq1 a b) : MEq1 b a :=
  match a, h with
  | .(b), MEq1.myrefl b => by

    exact MEq1.myrefl b

#print symm1

-- def symm1' (a b c : A) (h1 : MEq1 b c) (h : MEq1 a b) : MEq1 b a :=
--   match b, h with
--   | .(a), MEq1.myrefl b => MEq1.myrefl b

def symm2 (a b c : A) (h1 : MEq1 b c) (h : MEq1 a b) : MEq1 b a :=
  match h with
  | MEq1.myrefl a => MEq1.myrefl a

-- def symm3 (a b c : A) (h1 : MEq1 b c) (h : MEq1 a b) : MEq1 b a :=
--   match c, c, h with
--   | .(a), .(b), MEq1.myrefl c => MEq1.myrefl c

inductive List (A : Type) : Type where
| nil : List A
| cons : A → List A → List A

def map {A B : Type} (f : A → B) (xs : List A) : List B :=
  match xs with
  | .nil => List.nil
  | .cons x xs' => List.cons (f x) (map f xs')

inductive List1 : Type → Type where
| nil A : List1 A
| cons A : A → List1 A → List1 A

def map1 {A B : Type} (f : A → B) (xs : List1 A) : List1 B :=
  match xs with
  | List1.nil A => List1.nil B
  | List1.cons A x xs' => List1.cons B (f x) (map1 f xs')

inductive Vec : Type → Nat → Type where
| nil : (A : Type) → Vec A .zero
| nil1 : A → Vec A .zero

-- def a := (Vec.nil1 2)
-- def b := (Vec.nil1 )
-- | cons A

def absurd : (A : Type) → False -> A
  | B, hF => hF.elim

end My
