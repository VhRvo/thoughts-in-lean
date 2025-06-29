import Mathlib.Data.Set.Basic

-- Method 1: Using Set.range (most common)
def image_as_range (f : α → β) : Set β := Set.range f

-- Method 2: Using set-builder notation with ∃
def image_as_exists (f : α → β) : Set β := {y | ∃ x, f x = y}

-- Method 3: More explicit set-builder notation
def image_explicit (f : α → β) : Set β := {f x | x : α}

-- Method 4: If you want to restrict to a specific set A ⊆ α
def image_on_set (f : α → β) (A : Set α) : Set β := f '' A
-- This is equivalent to: {f x | x ∈ A}

-- Examples of usage:
example (f : ℕ → ℕ) : Set.range f = {y | ∃ x, f x = y} := by
  rfl

example (f : ℕ → ℕ) : Set.range f = {f x | x : ℕ} := by
  rfl

-- If you specifically want the image of a set A
-- example (f : α → β) (A : Set α) :
--   f'' A = {y | ∃ x ∈ A, f x = y} := by
--   rfl

-- -- Alternative notation for image of a set
-- example (f : α → β) (A : Set α) :
--   f'' A = {f x | x ∈ A} := by
--   rfl
