set_option pp.proofs true

inductive PreInterval : Type where
| mk : (lower : Nat) → (upper : Nat) → PreInterval

#print PreInterval.mk.inj
#print PreInterval.noConfusion

inductive Interval : Type where
| mk : (lower : Nat) → (upper : Nat) → (h : lower ≤ upper) → Interval

#print Interval.mk.inj
