#print Nat.below

def natRec (n : Nat) (P : Nat → Prop) (p : (x : Nat) → @Nat.below P x → P x) : P n :=
  let step (n : Nat) (ih : @Nat.below P n) : PProd (P n) (@Nat.below P n) := PProd.mk (p n ih) ih
  -- We can obtain the corresponding induction hypothesis if we make `@Nat.below P n` as result.
  let below (n : Nat) : @Nat.below P n
        := Nat.recOn n PUnit.unit (λn' ih => step n' ih)
  p n (below n)
  -- match n with
  -- | .zero => p .zero PUnit.unit
  -- | .succ n' =>
  --    let h₁ := natRec n' P p
  --    let h₂ := p n'.succ h₁
  --    p n'.succ (PProd.mk h₁ _)

theorem Nat.acyclic (x : Nat) : x ≠ .succ (.succ x) := sorry
