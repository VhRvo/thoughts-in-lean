import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

open Function

def Initial (A : Type) := ∀ X : Type, ∃ f : A → X, ∀ g : A → X, f = g

def Isomorphic {A : Type} {B : Type} (f : A → B) :=
  ∃ g : B → A, LeftInverse g f ∧ RightInverse g f

def Iso (A : Type) (B : Type) :=
  ∃ f : A → B, Isomorphic f

def UniIso (A : Type) (B : Type) :=
  ∃ f : A → B, Isomorphic f ∧ (∀ g : A → B, Isomorphic g → f = g)

theorem uni_iso_if_initial : Initial A → Initial B → UniIso A B:= by
  unfold Initial UniIso Isomorphic RightInverse LeftInverse
  intro hIA hIB
  obtain ⟨f, hf⟩ := hIA B
  obtain ⟨g, hg⟩ := hIB A
  use f
  constructor
  { use g
    constructor
    { intro a
      obtain ⟨id', hid'⟩ := hIA A
      apply congr_fun (f := (g ∘ f)) (g := id)
      rw [←hid' (g ∘ f), ← hid' id] }
    { intro b
      obtain ⟨id', hid'⟩ := hIB B
      apply congr_fun (f := (f ∘ g)) (g := id)
      rw [←hid' (f ∘ g), ←hid' id] } }
  { intro g _
    exact hf g }

theorem initial_if_iso : Initial A → Iso A B → Initial B := by
  unfold Initial Iso Isomorphic RightInverse LeftInverse
  intro hIA hIso X
  obtain ⟨fAX, hfAX⟩ := hIA X
  obtain ⟨fAB, ⟨ fBA, _, hRI ⟩⟩ := hIso
  use fAX ∘ fBA
  intro fBX
  rw [hfAX (fBX ∘ fAB)]
  funext b
  simp
  rw [hRI b]

theorem initial_if_uni_iso : Initial A → UniIso A B → Initial B := by
  unfold Initial UniIso Isomorphic RightInverse LeftInverse
  intro hIA hUniIso
  obtain ⟨fAB, hIso, _hUnique ⟩ := hUniIso
  exact initial_if_iso hIA ⟨ fAB, hIso ⟩
