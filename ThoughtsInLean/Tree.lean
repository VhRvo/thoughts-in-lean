
inductive Tree : Type where
  | Leaf : Tree
  | Node : Tree → Tree → Tree

#print Tree.rec
#print Tree.recOn
#check Tree.recOn

def belowTree (P : Tree → Prop) : Tree → Prop
--  := λ tree => Tree.recOn tree True (λ left right left' right' => (left' ∧ P left) ∧ (right' ∧ P right))
  | .Leaf => True
  | .Node l r => (belowTree P l ∧ P l) ∧ (belowTree P r ∧ P r)


def treeRec₁ (tree : Tree) (P : Tree → Prop) (p : (tree : Tree) → (m : belowTree P tree) → P tree) : P tree :=
  let step (tree : Tree) (m : belowTree P tree) : belowTree P tree ∧ P tree := And.intro m (p tree m)
  let below (tree : Tree) : belowTree P tree := Tree.recOn tree True.intro (λ left right left' right' => And.intro (step left left') (step right right'))
  -- let rec below (tree : Tree) : belowTree P tree :=
  --   match tree with
  --   | .Leaf => True.intro
  --   | .Node left right => And.intro (step left (below left)) (step right (below right))
  p tree (below tree)

#print PProd
#print PUnit

#print Tree.below
#print Nat.below

def treeRec (tree : Tree) (P : Tree → Prop) (p : (tree : Tree) → (m : @Tree.below P tree) → P tree) : P tree :=
  let step (tree : Tree) (m : @Tree.below P tree) : PProd (P tree) (Tree.below tree) := PProd.mk (p tree m) m
  let below (tree : Tree) : @Tree.below P tree := Tree.recOn tree PUnit.unit (λ left right left' right' => PProd.mk (step left left') (step right right'))
  p tree (below tree)

#print treeRec
  -- match tree with
  -- | .Leaf => p .Leaf True.intro
  -- | .Node left right => sorry

def natRec (nat : Nat) (P : Nat → Prop) (p : (nat : Nat) → (m : @Nat.below P nat) → P nat) : P nat :=
  let step (nat : Nat) (m : @Nat.below P nat) : PProd (P nat) (Nat.below nat) := PProd.mk (p nat m) m
  let below  (nat  : Nat)  :  @Nat.below P nat := Nat.recOn nat PUnit.unit (λ inner inner' => (step inner inner'))
  p nat (below nat)

-- theorem acyclic (n : Nat) : n ≠ .succ (.succ (.succ n)) :=





inductive Vector (α : Type) : Nat → Type where
  | VNil : Vector α 0
  | VCos : α → {n : Nat} → Vector α n → Vector α (.succ n)

#print Vector.rec
#print Vector.recOn
