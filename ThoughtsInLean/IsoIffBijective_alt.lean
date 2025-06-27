import Mathlib
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

open Function

set_option pp.proofs true

variable {A B : Type}

theorem monic_iff_injective (f : A → B) :
    (∀ (C : Type) (s t : C → A), f ∘ s = f ∘ t → s = t) ↔
    (∀ a₁ a₂ : A, f a₁ = f a₂ → a₁ = a₂)
  := by
  constructor
  { intro h a₁ a₂ hf
    -- prove if the following defintions are using have instead of let
    have a₁' := fun () => a₁
    have ha₁ : a₁' () = a₁ := by
      sorry
      -- rfl
    have a₂' := fun () => a₂
    have comp_eq : f ∘ a₁' = f ∘ a₂' := by
      funext ()
      simp
      sorry
      -- rw [a₁']
      -- unfold [a₁']
      -- rw [a₁', a₂']
      -- exact hf
    sorry }
  { intro h C s t hfsft
    have hst : ∀ x : C, s x = t x := by
      intro x
      have hfst : f (s x) = f (t x) :=
        congr_fun hfsft x
      exact h (s x) (t x) hfst
    exact funext hst }

-- use `choose` and `choose_spec` functions instead of `choose` tactic.
theorem iso_iff_bijective (f : A → B) :
    (∃ g : B → A, LeftInverse g f ∧ RightInverse g f) ↔
    ∀ b : B, ∃! a : A, f a = b := by
  unfold RightInverse
  unfold LeftInverse
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
    let g := fun b => Classical.choose (h b)
    use g
    constructor
    { intro a
      unfold g
      obtain ⟨_, h2⟩ := Classical.choose_spec (h (f a))
      -- change Classical.choose (h b) with a'
      symm
      exact h2 a (Eq.refl (f a)) }
    { intro b
      unfold g
      obtain ⟨h1, _⟩ := Classical.choose_spec (h b)
      exact h1 } }
