-- import Std.Tactic.NoMatch

set_option pp.proofs true

def hello := "world"

theorem Nat.succ_neq_self (n : Nat) :
  Nat.succ n ≠ n :=
by
  induction n with
  | zero       => simp
  | succ n' ih => simp [ih]

#print Nat.succ_neq_self
#print List.reverse
#print List.noConfusion
