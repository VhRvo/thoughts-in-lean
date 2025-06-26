import Mathlib
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

open Function

set_option pp.proofs true

variable {A B : Type*}

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
    -- choose g a using h
    let g := fun b => Classical.choose (h b)
    use g
    constructor
    { intro a
      unfold g
      obtain ⟨_, h2⟩ := Classical.choose_spec (h (f a))
      symm
      exact h2 a (Eq.refl (f a)) }
    { intro b
      unfold g
      obtain ⟨h1, _⟩ := Classical.choose_spec (h b)
      exact h1 } }

theorem iso_iff_bijective.tactic (f : A → B) :
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
