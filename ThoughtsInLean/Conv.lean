-- example {α β} (f : α → β) (ha : α) : β := by
--   conv at ha =>
--     . exact f ha

example (a b c : Nat) : (b * c) * (b * c) * (b * c) = (b * c) * (c * b) * (c * b) := by
  conv in (occs := 2 3) (b * c) =>
    . rw [Nat.mul_comm]
    . rw [Nat.mul_comm]
