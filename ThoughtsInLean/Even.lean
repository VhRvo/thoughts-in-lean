set_option pp.proofs true

inductive Even : Nat → Prop where
| zero : Even 0
| succ : {n : Nat} → Even n → Even (n + 2)

theorem one_not_even (h : Even 1) : False :=
  nomatch h

theorem three_not_even (h : Even 3) : False :=
  nomatch h

-- #print three_not_even.

theorem not_even.tactic (h : Even 1) : False := by
  cases h

#print not_even.tactic

#print Nat.succ.inj

theorem not_even.manual (h : Even 1) : False :=
  let motive := fun (n : Nat) (h : Even n) => 1 ≠ n
  (@Even.rec
    motive
    (Nat.noConfusion)
    (fun {n : Nat} (h : Even n) (h' : motive n h) => fun h => Nat.noConfusion (Nat.succ.inj h))
    1
    h) (Eq.refl 1)
