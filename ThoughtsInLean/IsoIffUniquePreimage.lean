import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic

open Function

set_option pp.proofs true

variable {A B : Prop}

theorem witness {f : A → B} (h : ∀ (b : B), ∃! a, f a = b) (b : B) : A := by
  obtain ⟨x, _⟩  := h b
  exact x

theorem iso_iff_unique_preimage (f : A → B) :
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
    let g := fun b => (h b).fst
    use g
    constructor
    { intro a
      unfold g
      obtain ⟨w, h1, h2⟩ := h (f a)
      symm
      exact h2 a h1 }
    { intro b
      unfold g
      obtain ⟨w, h1, _⟩ := h b
      exact h1 } }

example (he : ∃! (x : A), x = x) : A := by
  obtain ⟨x, _⟩  := he
  exact x
