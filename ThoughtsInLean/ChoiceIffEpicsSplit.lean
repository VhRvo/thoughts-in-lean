import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
-- import Init.Classical

set_option pp.proofs true

open Function

variable {α β : Sort u}

-- theorem choice_iff_epics_split :
--     (∀ (f : α → β), Epic f → SplitEpic f) ↔
--     (∀ (S : ι → Type*), (∀ i : ι, Nonempty (S i) → ∃ f : (i : ι) → S i, True)) :=
--   sorry

def Epic (f : α → β) := ∀ (C : Type) (s t : β → C), ∀ a, s (f a) = t (f a) → ∀ b, s b = t b
def SplitEpic (f : α → β) := ∃ g : β → α, ∀ a, f (g a) = a
def global_choice_iff_epics_split :
    (∀ (f : α → β), Epic f → SplitEpic f) →
    (Nonempty α → α) := by
  unfold Epic SplitEpic
  intro h hn
  sorry

theorem epics_split_if_axiom_of_choice :
    (∀ (f : α → β), Surjective f → SplitEpic f) :=
  by
  unfold Surjective SplitEpic HasRightInverse RightInverse LeftInverse
  intro f hf
  -- { choose g h using hf
  --   use g }
  { let g : β → α := fun b => Classical.choose (hf b)
    use g
    intro b
    exact Classical.choose_spec (hf b) }

variable (p : A → Prop) (h : ∃ x, p x)

#check ((let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩ : Nonempty {x // p x}) : Nonempty _)
#check ((let ⟨x, px⟩ := h; Nonempty.intro ⟨x, px⟩ : Nonempty {x // p x}) : Nonempty _)
#check (let ⟨x, px⟩ := h; Nonempty.intro (Subtype.mk x px))

def fake_choice : Nonempty α → α := by sorry
#check Classical.choice

noncomputable def indefiniteDescription {A : Type} (p : A → Prop) (h : ∃ x, p x) : {x // p x} :=
  Classical.choice <| (let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩)
