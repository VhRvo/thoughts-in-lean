
namespace Demo

inductive LE : Nat → Nat → Prop where
| zero : (n : Nat) → LE 0 n
| succ : (m n : Nat) → LE m n → LE (Nat.succ m) (Nat.succ n)

-- theorem inv_zero1 {m : Nat} (h : LE m 0) : m = 0 :=
--   match h with
--   | LE.zero n => by
--     exact Eq.refl 0

theorem inv_zero {m : Nat} (h : LE m 0) : m = 0 :=
  match m, h with
  | .(0), LE.zero (Nat.zero) => by
    exact Eq.refl 0

theorem inv_zero₂ {m : Nat} (h : LE m 0) : m = 0 :=
  match m, h with
  | (0), LE.zero (Nat.zero) => by
    exact Eq.refl 0

theorem inv_zero₁ {m n : Nat} {he : n = 0} (h : LE m n) : m = 0 :=
  match m, n, h with
  | .(0), (_), LE.zero n => Eq.refl 0

theorem inv_zero₃ {m n : Nat} {he : n = 0} (h : LE m n) : m = 0 :=
  match m, n, h with
  | .(0), .(_), LE.zero n => Eq.refl 0

theorem inv_zero1 {m n : Nat} {he : n = 0} (h : LE m n) : m = 0 :=
  match m, h with
  | .(0), LE.zero n => Eq.refl 0

end Demo
