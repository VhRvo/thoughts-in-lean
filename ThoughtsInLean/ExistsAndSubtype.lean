-- Exists vs Subtype in Lean 4 from Claude
-- Demonstrating the key differences

import Mathlib
import Mathlib.Data.Nat.Basic

-- =============================================================================
-- 1. BASIC DEFINITIONS AND TYPES
-- =============================================================================

-- Exists is a proposition (lives in Prop)
#check ∃ n : ℕ, n > 5  -- This has type Prop

-- Subtype is a type (lives in Type)
#check {n : ℕ // n > 5}  -- This has type Type

-- =============================================================================
-- 2. CONSTRUCTION AND EXTRACTION
-- =============================================================================

-- Constructing an existence proof
example : ∃ n : ℕ, n > 5 := by
  use 10
  norm_num

-- Constructing a subtype element
example : {n : ℕ // n > 5} := ⟨10, by norm_num⟩

-- Different ways to extract information
example : ∃ n : ℕ, n > 5 := by
  use 10
  norm_num

noncomputable example (h : ∃ n : ℕ, n > 5) : ℕ := by
  -- We can extract the witness using Classical.choose
  exact Classical.choose h

-- With subtype, we can directly access components
example (x : {n : ℕ // n > 5}) : ℕ := x.val  -- or x.1
example (x : {n : ℕ // n > 5}) : x.val > 5 := x.property  -- or x.2

-- =============================================================================
-- 3. COMPUTATIONAL BEHAVIOR
-- =============================================================================

-- Exists: Not directly computational (requires classical axioms to extract)
noncomputable def extract_from_exists (h : ∃ n : ℕ, n > 5) : ℕ :=
  Classical.choose h

-- Subtype: Directly computational
def extract_from_subtype (x : {n : ℕ // n > 5}) : ℕ := x.val

-- Example showing the difference
def some_large_nat : {n : ℕ // n > 5} := ⟨100, by norm_num⟩

#eval extract_from_subtype some_large_nat  -- This works: outputs 100

-- This would require classical reasoning and isn't directly evaluable
def proof_exists : ∃ n : ℕ, n > 5 := ⟨100, by norm_num⟩
-- #eval extract_from_exists proof_exists  -- This won't work directly

-- =============================================================================
-- 4. PATTERN MATCHING AND DESTRUCTURING
-- =============================================================================

-- Exists: Must be destructured in proofs
example (h : ∃ n : ℕ, n > 5) : ∃ m : ℕ, m > 3 := by
  obtain ⟨n, hn⟩ := h
  use n
  omega

-- Subtype: Can be destructured directly
example (x : {n : ℕ // n > 5}) : {m : ℕ // m > 3} := by
  obtain ⟨n, hn⟩ := x
  use n
  omega
  -- exact ⟨x.val, by omega⟩

-- Or using pattern matching
def process_subtype : {n : ℕ // n > 5} → {m : ℕ // m > 3}
  | ⟨n, h⟩ => ⟨n, by omega⟩

-- =============================================================================
-- 5. TYPE VS PROPOSITION DISTINCTION
-- =============================================================================

-- Exists gives you a proof that something exists
theorem exists_demo : ∃ n : ℕ, n * n = 16 := by
  use 4
  -- norm_num

-- Subtype gives you the actual object with its property
def sqrt_16 : {n : ℕ // n * n = 16} := ⟨4, by norm_num⟩

-- You can convert between them
def subtype_to_exists (x : {n : ℕ // n > 5}) : ∃ n : ℕ, n > 5 :=
  ⟨x.val, x.property⟩

-- Going the other way requires classical choice
noncomputable def exists_to_subtype (h : ∃ n : ℕ, n > 5) : {n : ℕ // n > 5} :=
  Classical.indefiniteDescription _ h
  -- ⟨Classical.choose h, Classical.choose_spec h⟩

-- =============================================================================
-- 6. PRACTICAL USAGE PATTERNS
-- =============================================================================

-- Use Exists when you want to prove existence
theorem even_numbers_exist : ∃ n : ℕ, Even n := by
  use 2
  exact even_two

-- Use Subtype when you want to work with objects satisfying a property
def EvenNat : Type := {n : ℕ // Even n}

def double_even (x : EvenNat) : EvenNat := by
  cases' x with n hn
  use 2 * n
  unfold Even
  use n
  omega
  -- exact Even.two_mul n

-- =============================================================================
-- 7. FUNCTION DEFINITIONS
-- =============================================================================

-- With exists, you typically work in proof mode
noncomputable def function_with_exists (h : ∃ n : ℕ, n > 0) : ℕ := by
  obtain ⟨n, _⟩ := Classical.indefiniteDescription _ h
  exact n + 1

-- With subtype, you can work directly with the value
def function_with_subtype (x : {n : ℕ // n > 0}) : ℕ := x.val + 1

-- =============================================================================
-- 8. EQUALITY AND DECIDABILITY
-- =============================================================================

-- Subtype elements can be compared
def compare_subtypes (x y : {n : ℕ // n > 5}) : Bool := x.val = y.val
def compare_subtypes' (x y : {n : ℕ // n > 5}) : Bool := x = y

-- Exists propositions are about provability, not the specific witness
example (h1 h2 : ∃ n : ℕ, n > 5) : h1 = h2 := by
  -- All proofs of the same proposition are equal
  rfl

-- =============================================================================
-- 9. COERCIONS AND CONVENIENCE
-- =============================================================================

-- Lean can automatically coerce subtypes to their base type
example (x : {n : ℕ // n > 5}) : ℕ := x  -- Coerces to x.val

-- You can also use the coercion in arithmetic
example (x y : {n : ℕ // n > 5}) : ℕ := x + y

-- =============================================================================
-- 10. SIGMA TYPES RELATIONSHIP
-- =============================================================================

-- Subtype is actually defined using Sigma types
#check Subtype  -- {x // P x} is notation for Subtype P
#check Sigma    -- Σ x : α, β x

-- The key difference:
-- Σ x : α, β x  -- β depends on x and can be any type
-- {x : α // P x} -- P is always a proposition (Prop)

-- Example showing the relationship
-- def subtype_as_sigma (n : ℕ) : {x : ℕ // x > n} ≃ Σ x : ℕ, x > n := by
--   rfl  -- They're definitionally equal!

-- =============================================================================
-- 11. SUMMARY EXAMPLES
-- =============================================================================

-- When to use Exists: Proving theorems about existence
theorem prime_exists : ∃ p : ℕ, Nat.Prime p ∧ p > 10 := by
  use 11
  constructor
  · norm_num
  · norm_num

-- When to use Subtype: Working with constrained data
def PrimesAboveTen : Type := {p : ℕ // Nat.Prime p ∧ p > 10}

def next_prime_candidate (p : PrimesAboveTen) : ℕ := p.val + 2

-- Converting between them
def demo_conversion : PrimesAboveTen → ∃ p : ℕ, Nat.Prime p ∧ p > 10 :=
  fun p => ⟨p.val, p.property⟩

#check demo_conversion
