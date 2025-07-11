inductive Parity : Nat → Type where
  | even (h : Nat) : Parity (h + h)
  | odd (h : Nat) : Parity ((h + h) + 1)

#print Parity.rec

def Nat.parity (n : Nat) : Parity n :=
  match n with
  | 0 => .even 0
  | n' + 1 =>
    match n'.parity with
    | .even h => .odd h
    | .odd h =>
      have eq : (h + 1) + (h + 1) = (h + h + 1 + 1) :=
        by
        omega
      eq ▸ .even (h + 1)

def half (n : Nat) : Nat :=
  match n, n.parity with
  | .(h + h),     .even h => h
  | .(h + h + 1), .odd h  => h

def half₁ (n : Nat) : Nat :=
  match n.parity with
  | .even h => h
  | .odd h  => h

-- type mismatch
--   Parity.even h
-- has type
--   Parity (h + h) : Type
-- but is expected to have type
--   Parity n : Type
-- def half₂ (n : Nat) : Nat :=
--   match n.parity, n with
--   | .even h , .(h + h)=> h
--   | .odd h, .(h + h + 1)  => h
