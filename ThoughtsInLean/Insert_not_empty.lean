import Std.Data.HashSet
import Batteries.Logic
import Mathlib.Tactic

-- namespace HashSet
open Std

variable {α : Type u} [DecidableEq α] [Hashable α] {v : α}

-- https://x.com/Aron_Adler/status/1921654852167352504
theorem verbose.insert_not_empty : ∀ (m : HashSet α), m.insert v ≠ ∅ := by
  have insert_isEmpty_is_false : ∀ (m : HashSet α), (m.insert v).isEmpty = false := by
    intro m
    simp [HashSet.isEmpty_insert]
  intro m h
  have applied := insert_isEmpty_is_false m
  rw [h] at applied
  simp at applied

theorem ugly.insert_not_empty : ∀ (m : HashSet α), m.insert v ≠ ∅ := by
  intro m h
  have applied := HashSet.isEmpty_insert (m := m) (a := v)
  rw [h] at applied
  simp at applied

-- https://x.com/haskallcurry/status/1921668005697638759
theorem neat.insert_not_empty : ∀ (m : HashSet α), m.insert v ≠ ∅ := by
  intro m h
  apply congr_fun ∘ congr_arg (HashSet.contains) at h
  -- apply congr_arg (HashSet.contains) at h; apply congr_fun at h
  specialize h v
  conv at h =>
    congr
    { simp }
    { simp }
  simp at h
