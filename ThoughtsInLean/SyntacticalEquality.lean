
def double (n : Nat) : Nat := n + n

-- α-conversion: syntactical equality
example {f : α → β} (h : (fun x ↦ f x) = (fun y ↦ f y)) : (fun z ↦ f z) = (fun v ↦ f v) := by
  rw [h] -- can apply syntactical equality

-- β-conversion: definitional equality
example {f : α → β} {a : α} (h : (fun x ↦ f x) a = f a) : f a = f a := by
  -- rw [h] -- cannot apply syntactical equality
  exact h

-- δ-conversion: definitional equality
example (h : double 5 = 5 + 5) : 5 + 5 = 5 + 5 := by
  -- rw [h] -- cannot apply syntactical equality
  exact h

-- ζ-conversion: syntactical equality
example (h : (let n : Nat := 2; n + n) = 2 + 2) : 2 + 2 = 2 + 2 := by
  rw [h] -- can apply syntactical equality

-- η-conversion: definitional equality
example {f : α → β} (h : (fun x ↦ f x) = f) : f = f := by
  -- rw [h] -- cannot apply syntactical equality
  exact h

-- η-conversion: definitional equality
example {f : α → β} (h : (fun x ↦ f x) = f) : f = f := by
  -- rw [h] -- cannot apply syntactical equality
  exact h

-- ι-conversion: definitional equality
example (h : Prod.fst (a, b) = a) : a = a := by
  -- rw [h] -- cannot apply syntactical equality
  exact h
