-- Axiom of Choice equivalent to "all epimorphisms split"
-- This proof works in the category of sets (Type*)

import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic

-- Define what it means for a function to be surjective (epic in Set)
def Surjective {α β : Type*} (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

-- Define what it means for a surjective function to split
def Splits {α β : Type*} (f : α → β) (hf : Surjective f) : Prop :=
  ∃ g : β → α, ∀ b : β, f (g b) = b

-- The main theorem: Axiom of Choice is equivalent to all epics splitting
theorem axiom_of_choice_iff_epics_split :
  (∀ {α β : Type} (f : α → β), Surjective f → ∃ g : β → α, ∀ b : β, f (g b) = b) ↔
  (∀ {ι : Type} (S : ι → Type), (∀ i : ι, Nonempty (S i)) → ∃ f : (i : ι) → S i, True) :=
by
  constructor
  -- Direction 1: If all epics split, then we have choice
  · intro h ι S hS
    -- We'll construct a choice function using the splitting property
    -- First, define the disjoint union
    let T := Σ i : ι, S i
    -- Define the projection function
    let π : T → ι := fun ⟨i, _⟩ => i

    -- Show π is surjective
    have hπ_surjective : Surjective π := by
      intro i
      -- Since S i is nonempty, we can find an element
      obtain ⟨s⟩ := hS i
      use ⟨i, s⟩

    -- Apply our hypothesis to get a splitting
    obtain ⟨σ, hσ⟩ := @h T ι π hπ_surjective

    -- Extract the choice function
    let choice : (i : ι) → S i := fun i => (σ i).2

    -- Verify this works
    use choice
    -- trivial

  -- Direction 2: If we have choice, then all epics split
  · intro choice α β f hf
    -- Use choice to select a preimage for each element of β
    let preimage_sets : β → Type* := fun b => ({a : α // f a = b})

    -- Show each preimage set is nonempty
    have h_nonempty : ∀ b : β, Nonempty (preimage_sets b) := by
      intro b
      obtain ⟨a, ha⟩ := hf b
      exact ⟨⟨a, ha⟩⟩

    -- Apply choice to get a selection function
    obtain ⟨select, _⟩ := choice preimage_sets h_nonempty

    -- Define the splitting map
    let g : β → α := fun b => (select b).val

    -- Verify the splitting property
    use g
    intro b
    exact (select b).property

-- Alternative formulation using Classical choice
theorem epics_split_using_classical_choice :
  ∀ {α β : Type*} (f : α → β), Surjective f → ∃ g : β → α, ∀ b : β, f (g b) = b :=
by
  intros α β f hf
  -- Use classical choice directly
  let g : β → α := fun b => Classical.choose (hf b)
  use g
  intro b
  exact Classical.choose_spec (hf b)

-- Show that our splitting property implies choice
theorem splitting_implies_choice :
  (∀ {α β : Type*} (f : α → β), Surjective f → ∃ g : β → α, ∀ b : β, f (g b) = b) →
  (∀ (ι : Type*) (S : ι → Set α), (∀ i : ι, (S i).Nonempty) → ∃ f : ι → α, ∀ i : ι, f i ∈ S i) :=
by
  intro h ι α S hS
  -- Construct the disjoint union
  let T := Σ i,  S i
  let π : T → ι := Sigma.fst

  -- π is surjective
  have hπ : Surjective π := by
    intro i
    obtain ⟨a, ha⟩ := hS i
    use ⟨i, a, ha⟩

  -- Get splitting
  obtain ⟨σ, hσ⟩ := h π hπ

  -- Extract choice function
  use fun i => (σ i).2.1
  intro i
  exact (σ i).2.2

-- The converse: choice implies splitting (already shown above)
theorem choice_implies_splitting :
  (∀ {ι : Type*} (S : ι → Set α), (∀ i : ι, (S i).Nonempty) → ∃ f : ι → α, ∀ i : ι, f i ∈ S i) →
  (∀ {α β : Type*} (f : α → β), Surjective f → ∃ g : β → α, ∀ b : β, f (g b) = b) :=
by
  intros choice α β f hf
  -- For each b, consider the preimage set
  let preimages : β → Set α := fun b => {a : α | f a = b}

  -- Each preimage is nonempty
  have h_nonempty : ∀ b : β, (preimages b).Nonempty := by
    intro b
    obtain ⟨a, ha⟩ := hf b
    use a
    exact ha
  -- Apply choice
  obtain ⟨g, hg⟩ := choice preimages h_nonempty
  use g
  intro b
  exact hg b

#check axiom_of_choice_iff_epics_split
#check epics_split_using_classical_choice
#check splitting_implies_choice
#check choice_implies_splitting
