import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Init.Prelude

open Function
#print id

def Initial (α : Type) := ∀ X : Type, ∃ f : α → X, ∀ g : α → X, f = g

def Terminal (α : Type) := ∀ X : Type, ∃ f : X → α, ∀ g : X → α, f = g

-- def LocalTerminal (α : Type) [LE α] (t : α) := ∃ p : α → Prop , ∀ x, p x → x ≤ t

def Isomorphic {α β : Type} (f : α → β) :=
  ∃ g : β → α, g ∘ f = id ∧ f ∘ g = id

def Iso (α β : Type) :=
  ∃ f : α → β, Isomorphic f

def UniIso (α β : Type) :=
  ∃ f : α → β, Isomorphic f ∧ (∀ g : α → β, Isomorphic g → f = g)

structure Product.object {α β : Type} (γ : Type) where
  π₀ : γ → α
  π₁ : γ → β

structure Product.arrow
    {α β γ γ' : Type}
    (C : @Product.object α β γ)
    (D : @Product.object α β γ') where
  arr : γ → γ'
  hom : C.π₀ = D.π₀ ∘ arr ∧ C.π₁ = D.π₁ ∘ arr

def Product.identity
    {α β γ : Type}
    {obj : @Product.object α β γ} : Product.arrow obj obj :=
  Product.arrow.mk id (by
    constructor
    { symm; exact Function.comp_id obj.π₀ }
    { symm; exact Function.comp_id obj.π₁ })

def Product.compose
    {α β γα γβ γγ : Type}
    {A : @Product.object α β γα}
    {B : Product.object γβ}
    {C : Product.object γγ}
    : Product.arrow B C → Product.arrow A B → Product.arrow A C := by
  intro g f
  apply Product.arrow.mk (g.arr ∘ f.arr)
  constructor
  { rw [f.hom.left, g.hom.left, Function.comp_assoc] }
  { rw [f.hom.right, g.hom.right, Function.comp_assoc] }

def Product.id_comp
    {α β γα γβ : Type}
    {A : @Product.object α β γα}
    {B : Product.object γβ}
    {f : Product.arrow A B}
    : Product.compose Product.identity f = f := by
  unfold Product.compose Product.identity
  simp [Function.id_comp f.arr]

def Product.id_comp₁
    {α β γα γβ : Type}
    {A : @Product.object α β γα}
    {B : Product.object γβ}
    {f : Product.arrow A B}
    : Product.compose Product.identity f = f := by
  cases f with
  | mk f_arr f_hom =>
    unfold Product.compose Product.identity
    rfl

def Product.comp_id
    {α β γα γβ : Type}
    {A : @Product.object α β γα}
    {B : Product.object γβ}
    {f : Product.arrow A B}
    : Product.compose f Product.identity = f := by
  unfold Product.compose Product.identity
  simp [Function.comp_id f.arr]

def Product.comp_assoc
    {α β γα γβ γγ γγ' : Type}
    {A : @Product.object α β γα}
    {B : Product.object γβ}
    {C : Product.object γγ}
    {D : Product.object γγ'}
    {f : Product.arrow C D}
    {g : Product.arrow B C}
    {h : Product.arrow A B} :
    Product.compose (Product.compose f g) h =
    Product.compose f (Product.compose g h) := by
  unfold Product.compose
  simp [Function.comp_assoc]

def Product.Isomorphic
    {α β γ γ' : Type}
    {C : @Product.object α β γ} {D : Product.object γ'}
    (f : Product.arrow C D) :=
  ∃ (g : Product.arrow D C),
    Product.compose g f = Product.identity ∧
    Product.compose f g = Product.identity

def Product.Iso
    {α β γ γ' : Type}
    (C : @Product.object α β γ) (D : Product.object γ') :=
  ∃ (f : Product.arrow C D), Product.Isomorphic f

def Product.UniIso
    {α β γ γ' : Type}
    (C : @Product.object α β γ) (D : Product.object γ') :=
  ∃ (f : Product.arrow C D),
    Product.Isomorphic f ∧ (∀ f' : Product.arrow C D, Product.Isomorphic f' → f = f')

def IsProduct
   {α β γ : Type}
   (C : @Product.object α β γ) :=
  ∀ (γ' : Type) (D : @Product.object α β γ'),
  ∃ k : Product.arrow D C,
  ∀ k' : Product.arrow D C, k = k'
  -- ∃! k : γ' → γ, D.π₀ = C.π₀ ∘ k ∧ D.π₁ = C.π₁ ∘ k

def Void (α : Type) := ∀ _ : α, False

def Single (α : Type) := ∃ x : α, ∀ y : α, x = y


theorem uni_iso_if_initial : Initial α → Initial β → UniIso α β:= by
  unfold Initial UniIso Isomorphic
  intro hIA hIB
  obtain ⟨f, hf⟩ := hIA β
  obtain ⟨g, hg⟩ := hIB α
  use f
  constructor
  { use g
    constructor
    { obtain ⟨id', hid'⟩ := hIA α
      rw [←hid' (g ∘ f), ← hid' id] }
    { obtain ⟨id', hid'⟩ := hIB β
      rw [←hid' (f ∘ g), ←hid' id] } }
  { intro g _
    exact hf g }


theorem initial_if_iso : Initial α → Iso α β → Initial β := by
  unfold Initial Iso Isomorphic
  intro hIA hIso X
  obtain ⟨fAX, hfAX⟩ := hIA X
  obtain ⟨fAB, ⟨ fBA, _, hRI ⟩⟩ := hIso
  use fAX ∘ fBA
  intro fBX
  rw [hfAX (fBX ∘ fAB)]
  rw [Function.comp_assoc, hRI, Function.comp_id]


theorem initial_if_uni_iso : Initial α → UniIso α β → Initial β := by
  unfold Initial UniIso Isomorphic
  intro hIA hUniIso
  obtain ⟨fAB, hIso, _hUnique ⟩ := hUniIso
  exact initial_if_iso hIA ⟨ fAB, hIso ⟩


theorem uni_iso_if_terminal : Terminal α → Terminal β → UniIso α β:= by
  unfold Terminal UniIso Isomorphic
  intro hIA hIB
  obtain ⟨f, hf⟩ := hIB α
  obtain ⟨g, hg⟩ := hIA β
  use f
  constructor
  { use g
    constructor
    { funext a
      obtain ⟨id', hid'⟩ := hIA α
      apply congr_fun (f := (g ∘ f)) (g := id)
      rw [←hid' (g ∘ f), ← hid' id] }
    { funext b
      obtain ⟨id', hid'⟩ := hIB β
      apply congr_fun (f := (f ∘ g)) (g := id)
      rw [←hid' (f ∘ g), ←hid' id] } }
  { intro g _
    exact hf g }


theorem terminal_if_iso : Terminal α → Iso α β → Terminal β := by
  unfold Terminal Iso Isomorphic
  intro hTA hIso X
  obtain ⟨fXA, hfXA⟩ := hTA X
  obtain ⟨fAB, ⟨ fBA, _, hRI ⟩⟩ := hIso
  use fAB ∘ fXA
  intro fXB
  rw [hfXA (fBA ∘ fXB), ←comp_assoc, hRI, id_comp]


theorem terminal_if_uni_iso : Terminal α → UniIso α β → Terminal β := by
  unfold Terminal UniIso Isomorphic
  intro hTA hUniIso
  obtain ⟨fAB, hIso, _hUnique ⟩ := hUniIso
  exact terminal_if_iso hTA ⟨ fAB, hIso ⟩


theorem void_uni_iso_void : Void α → Void β → UniIso α β := by
  unfold Void UniIso Isomorphic
  intro hA hB
  let f : α → β := fun a => (hA a).elim
  let g : β → α := fun b => (hB b).elim
  use f
  constructor
  { use g
    constructor
    { funext a
      exact (hA a).elim }
    { funext b
      exact (hB b).elim } }
  { intro _ _
    funext a
    exact (hA a).elim }


theorem single_uni_iso_single : Single α → Single β → UniIso α β := by
  unfold Single UniIso Isomorphic
  intro ⟨a, ha⟩ ⟨b, hb⟩
  let f : α → β := fun _ => b
  let g : β → α := fun _ => a
  use f
  constructor
  { use g
    constructor
    { funext x
      unfold g
      simp
      exact ha x }
    { funext x
      unfold f
      simp
      exact hb x } }
  { intro f' _
    funext x
    unfold f
    exact hb (f' x) }


theorem uni_iso_if_product
    (C : @Product.object α β γ) (D : Product.object γ')
    : IsProduct C → IsProduct D → Product.UniIso C D := by
  unfold IsProduct Product.UniIso Product.Isomorphic
  intro C.uni D.uni
  obtain ⟨f, f.uni⟩ := D.uni γ C
  obtain ⟨g, g.uni⟩ := C.uni γ' D
  have hgf : Product.compose g f = Product.identity := by
    { obtain ⟨id', id'.uni⟩ := C.uni γ C
      rw [←id'.uni Product.identity, id'.uni (Product.compose g f)] }
  have hfg : Product.compose f g = Product.identity := by
    { obtain ⟨id', id'.uni⟩ := D.uni γ' D
      rw [←id'.uni Product.identity, id'.uni (Product.compose f g)] }
  use f
  constructor
  { use g }
  { intro f' _
    exact f.uni f' }


theorem uni'_if_product
    (C : @Product.object α β γ) (D : @Product.object α β γ')
    : IsProduct C → IsProduct D → Iso γ γ' := by
  intro C.uni D.uni
  obtain ⟨ f, ⟨ g, hgf, hfg⟩ , f.uni ⟩  := uni_iso_if_product C D C.uni D.uni
  use f.arr
  { use g.arr
    constructor
    { exact congr_arg Product.arrow.arr hgf }
    { exact congr_arg Product.arrow.arr hfg } }


-- Perhaps the following theorem is unprovable.
theorem uni_iso'_if_product
    (C : @Product.object α β γ) (D : @Product.object α β γ')
    : IsProduct C → IsProduct D → UniIso γ γ' := by
  intro C.uni D.uni
  obtain ⟨f, ⟨g, hgf, hfg⟩, f.uni⟩  := uni_iso_if_product C D C.uni D.uni
  use f.arr
  constructor
  { use g.arr
    constructor
    { exact congr_arg Product.arrow.arr hgf }
    { exact congr_arg Product.arrow.arr hfg } }
  { intro f' f'.iso
    show f.arr = f'
    sorry }


theorem product_if_uni_iso
    (C : @Product.object α β γ) (D : Product.object γ')
    : IsProduct C → Product.UniIso C D → IsProduct D := by
  unfold IsProduct Product.UniIso Product.Isomorphic
  intro C.uni hUniIso γ'' D'
  obtain ⟨g', hg'⟩ := C.uni γ'' D'
  obtain ⟨f, ⟨ g'', _, hfg'' ⟩  , _ ⟩ := hUniIso
  use Product.compose f g'
  intro k'
  rw [hg' (Product.compose g'' k'), ←Product.comp_assoc, hfg'', Product.id_comp]


theorem Product.Prod
    : ∃ P : @Product.object α β (α × β), IsProduct P := by
  unfold IsProduct
  let P := @Product.object.mk α β (α × β) Prod.fst Prod.snd
  use P
  intro γ' D
  let f : γ' → α × β :=
    fun c => ⟨ D.π₀ c , D.π₁ c ⟩
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
  let _ := k.hom
  let _ := k'.hom
  let heπ₀ : P.π₀ ∘ k.arr = P.π₀ ∘ k'.arr := k.hom.left.symm.trans k'.hom.left
  let heπ₁ : P.π₁ ∘ k.arr = P.π₁ ∘ k'.arr := k.hom.right.symm.trans k'.hom.right
  unfold P
  let h : k.arr = k'.arr := by
    funext x
    let he1 := congr_fun heπ₀ x
    let he2 := congr_fun heπ₁ x
    unfold P at he1 he2
    simp at he1 he2
    let result := congr_arg₂ Prod.mk he1 he2
    exact result
  obtain ⟨ x, y ⟩ := k
  { obtain ⟨x', _⟩ := k'
    { simp
      exact h } }
