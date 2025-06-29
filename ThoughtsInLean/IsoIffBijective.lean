import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

open Function

set_option pp.proofs true

variable {A B : Type}

def Monic (f : A → B) := ∀ (C : Type) (s t : C → A), f ∘ s = f ∘ t → s = t

def SplitMonic (f : A → B) := HasLeftInverse f

def Isomorphic f :=
  ∃ g : B → A, LeftInverse g f ∧ RightInverse g f

def Epic (f : A → B) := ∀ (C : Type) (s t : B → C), s ∘ f = t ∘ f → s = t

def SplitEpic (g : B → A) := HasRightInverse g

def Image (f : A → B) : Set B
  := { b : B | ∃ a, b = f a }

#print Set.range

theorem monic_if_split_monic (f : A → B) :
    SplitMonic f →
    Monic f
  := by
  unfold SplitMonic HasLeftInverse LeftInverse Monic
  intro ⟨g, hLI⟩ C s t hfst
  -- funext c
  have h : (c : C) → s c = t c := by
    intro c
    have h1 : g ∘ (f ∘ s) = g ∘ (f ∘ t) :=
      congr_arg (g ∘ ·) hfst
    have h2 : g (f (s c)) = g (f (t c)) :=
      congr_fun h1 c
    rw [← hLI (s c), h2, hLI (t c)]
  exact funext h

-- theorem left_inverse_if_monic (f : A → B) :
--     Monic f →
--     SplitMonic f
--   := by
--   unfold SplitMonic HasLeftInverse LeftInverse
--   intro hex
--   sorry

theorem monic_iff_injective (f : A → B) :
    Monic f ↔ Injective f
  := by
  unfold Monic Injective
  constructor
  { intro h a₁ a₂ hf
    let a₁' := fun () => a₁
    let a₂' := fun () => a₂
    have hfa₁a₂ : f (a₁' ()) = f (a₂' ()) := hf
    have hf' : f ∘ a₁' = f ∘ a₂' := funext (fun () => hfa₁a₂)
    have h' := h Unit a₁' a₂' hf'
    exact congr_fun h' () }
  { intro h C s t hfsft
    have hst : ∀ x : C, s x = t x := by
      intro x
      have hfst : f (s x) = f (t x) :=
        congr_fun hfsft x
      exact h hfst
    exact funext hst }

theorem epic_iff_surjective [DecidableEq B] (f : A → B) :
    (∀ (C : Type) (s t : B → C), s ∘ f = t ∘ f → s = t) ↔ (∀ b, ∃ a : A, f a = b) := by
  constructor
  { intro h b
    contrapose! h
    use Bool, (fun _ => true), (fun x => x ≠ b)
    constructor
    { funext a
      simp [Function.comp]
      exact h a }
    { intro hf
      let h₁ := congr_fun hf b
      simp at h₁ } }
  { intro h C s t heq
    funext b
    obtain ⟨w, hw⟩ := h b
    rw [←hw]
    exact congr_fun heq w }

theorem epic_iff_onto (f : A → B) :
    Surjective f ↔ Set.range f = Set.univ
  := by
  unfold Surjective Set.range Set.univ
  constructor
  { intro h
    ext x
    constructor
    { intro _
      trivial }
    { intro _
      exact h x } }
  { intro h b
    have hex : ∃ a, f a = b := by
      have hT : b ∈ {_a | True} := trivial
      rw [←h] at hT
      exact hT
    obtain ⟨a, ha⟩ := hex
    use a }

theorem isomorphic_iff_bijective (f : A → B) :
    Isomorphic f ↔
    ∀ b : B, ∃! a : A, f a = b := by
  unfold Isomorphic RightInverse LeftInverse
  constructor
  { intro ⟨g, hgf, hfg⟩ b
    let a := g b
    use a
    constructor
    { exact hfg b }
    { intro a' ha'
      calc
        a' = g (f a') := (hgf a').symm
        _  = g b := by rw [ha']
        _  = a := by rfl } }
  { intro h
    choose g h using h
    use g
    constructor
    { intro a
      obtain ⟨_, h2⟩ := h (f a)
      symm
      exact h2 a (Eq.refl (f a)) }
    { intro b
      obtain ⟨h1, _⟩ := h b
      exact h1 } }

theorem monic_if_isomorphic (f : A → B) :
    Isomorphic f → Monic f
  := by
  unfold Isomorphic RightInverse LeftInverse Monic
  intro hex C s t h

  sorry

theorem epic_if_isomorphic (f : A → B) :
    Isomorphic f → Epic f
  := by
  unfold Isomorphic RightInverse LeftInverse Epic
  intro hex C s t h
  sorry
