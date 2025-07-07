import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Init.Prelude

open Function

structure Product.object {α β : Type} (γ : Type) where
  π₀ : γ → α
  π₁ : γ → β

structure Product.arrow
    {α β γ γ' : Type}
    (C : @Product.object α β γ)
    (D : @Product.object α β γ') where
  arr : γ → γ'
  hom : C.π₀ = D.π₀ ∘ arr ∧ C.π₁ = D.π₁ ∘ arr

 def IsProduct
   {α β γ : Type}
   (C : @Product.object α β γ) :=
  ∀ (γ' : Type) (D : @Product.object α β γ'),
  ∃ k : Product.arrow D C,
  ∀ k' : Product.arrow D C, k = k'

theorem Product.Prod
    : ∃ P : @Product.object α β (α × β), IsProduct P := by
  unfold IsProduct
  let P := @Product.object.mk α β (α × β) Prod.fst Prod.snd
  use P
  intro γ' D
  let f : γ' → α × β :=
    fun c => ⟨D.π₀ c , D.π₁ c⟩
  let k : Product.arrow D P := by
    apply Product.arrow.mk f
    { constructor
      { funext x
        unfold P f
        simp }
      { funext x
        unfold P f
        simp } }
  use k
  intro k'
  unfold P k
  obtain ⟨arr', hom⟩ := k'
  simp
  funext x
  let heπ₀ : P.π₀ ∘ f = P.π₀ ∘ arr' := k.hom.left.symm.trans hom.left
  let heπ₁ : P.π₁ ∘ f = P.π₁ ∘ arr' := k.hom.right.symm.trans hom.right
  let he1 := congr_fun heπ₀ x
  let he2 := congr_fun heπ₁ x
  exact congr_arg₂ Prod.mk he1 he2
