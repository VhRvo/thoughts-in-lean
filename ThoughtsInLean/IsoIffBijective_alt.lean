import Mathlib
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs

open Function

set_option pp.proofs true

variable {A B : Type}

theorem epic_iff_surjective₃ [DecidableEq B] (f : A → B) :
    (∀ (C : Type) (s t : B → C), s ∘ f = t ∘ f → s = t) ↔ (∀ b, ∃ a : A, f a = b) := by
  constructor
  { intro h b
    contrapose! h
    use Bool, (fun _ => true), (fun x => x ≠ b)
    constructor
    { funext a
      unfold Function.comp
      simp -- what behind the `simp`
      exact h a }
    { intro hf
      let h₁ := congr_fun hf b
      simp at h₁ } }
  { intro h C s t heq
    funext b
    -- what? `rfl` do magic thing.
    obtain ⟨a, rfl⟩ := h b
    exact congr_fun heq a }

theorem epic_iff_surjective₂ [DecidableEq B] (f : A → B) :
    (∀ (C : Type) (s t : B → C), s ∘ f = t ∘ f → s = t) ↔ (∀ b, ∃ a : A, f a = b) := by
  constructor
  { intro h b
    contrapose! h
    use Bool, (fun _ => true), (fun x => x ≠ b)
    constructor
    { funext a
      unfold Function.comp
      simp
      exact h a }
    { intro hf
      let h₁ := congr_fun hf b
      simp at h₁ } }
  { intro h C s t heq
    funext b
    -- what? `rfl` do magic thing.
    obtain ⟨a, rfl⟩ := h b
    exact congr_fun heq a }

theorem epic_iff_surjective₁ [DecidableEq B] (f : A → B) :
    (∀ (C : Type) (s t : B → C), s ∘ f = t ∘ f → s = t) ↔ (∀ b, ∃ a : A, f a = b)
  := by
  constructor
  { intro h b
    contrapose! h
    let C := Bool
    let s : B → C := fun _ => true
    let t : B → C := fun x => if x = b then false else true
    use C, s, t
    constructor
    { funext a
      simp [s, t]
      rw [if_neg]
      exact h a }
    { intro h₁
      have h₂ := congr_fun h₁ b
      simp [s, t] at h₂ } }
  { intro h C s t heq
    funext b
    obtain ⟨w, hw⟩ := h b
    nth_rewrite 1 [←hw]
    unfold Function.comp at heq
    let h := congr_fun heq w
    rw [congr_fun heq w, hw] }

theorem epic_iff_surjective [DecidableEq B] (f : A → B) :
    (∀ (C : Type) (s t : B → C), s ∘ f = t ∘ f → s = t) ↔ (∀ b, ∃ a : A, f a = b)
  := by
  constructor
  { intro h b
    contrapose! h
    let C := Bool
    let s : B → C := fun _ => true
    let t : B → C := fun x => if x = b then false else true
    use C, s, t
    constructor
    { funext a
      simp [s, t]
      rw [if_neg]
      exact h a }
    { intro h₁
      have h₂ := congr_fun h₁ b
      simp [s, t] at h₂ } }
  { intro h C s t heq
    funext b
    obtain ⟨w, hw⟩ := h b
    nth_rewrite 1 [←hw]
    unfold Function.comp at heq
    let h := congr_fun heq w
    rw [congr_fun heq w, hw] }

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
  -- My stupid solution
  { intro h b
    contrapose! h
    intro h_set_eq
    have h₁ : b ∈ {_a | True} := trivial
    rw [←h_set_eq] at h₁
    obtain ⟨w, hw⟩ := h₁
    apply h w
    exact hw }

-- interesting
theorem monic_iff_injective₁ (f : A → B) :
    (∀ (C : Type) (s t : C → A), f ∘ s = f ∘ t → s = t) ↔
    (∀ a₁ a₂ : A, f a₁ = f a₂ → a₁ = a₂)
  := by
  constructor
  { intro h a₁ a₂ hf
    -- The point of this proof is there is at least a element in some set
    let a₁' := fun _ : Bool => a₁
    let a₂' := fun _ : Bool => a₂
    have hf' : f ∘ a₁' = f ∘ a₂' :=
      funext (fun b =>
        match b with
        | .true => hf
        | .false => hf)
    have h' := h Bool a₁' a₂' hf'
    exact congr_fun h' true }
  { intro h C s t hfsft
    have hst : ∀ x : C, s x = t x := by
      intro x
      have hfst : f (s x) = f (t x) :=
        congr_fun hfsft x
      exact h (s x) (t x) hfst
    exact funext hst }

theorem monic_iff_injective₂ (f : A → B) :
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
