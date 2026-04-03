import Mathlib
/-

# Components of sum

Show `α ⊕ β ≃ β ⊕ α`.

-/
def swap {α β : Type} (s : α ⊕ β) : β ⊕ α :=
  match s with
  | Sum.inl a => Sum.inr a
  | Sum.inr b => Sum.inl b

example (α β : Type) (s : α ⊕ β)
  : swap (swap s) = s
:= by
  cases s
  · rfl
  · rfl

lemma swap_swap {α β : Type} (s : α ⊕ β)
  : swap (swap s) = s
:= by
  cases s <;> rfl

example (α β γ : Type) : α ⊕ β ≃ β ⊕ α where
  toFun := swap
  invFun := swap
  left_inv := by
    intro s
    exact swap_swap s
  right_inv := by
    intro s
    exact swap_swap s
/-

Show `(α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ)`.

-/
def assoc {α β γ : Type} :
  (α ⊕ β) ⊕ γ → α ⊕ (β ⊕ γ)
  :=
  λ s ↦ match s with
  | Sum.inl (Sum.inl a) => Sum.inl a
  | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
  | Sum.inr c           => Sum.inr (Sum.inr c)

def unassoc {α β γ : Type} :
  α ⊕ (β ⊕ γ) → (α ⊕ β) ⊕ γ
  :=
  λ s ↦ match s with
  | Sum.inl a           => Sum.inl (Sum.inl a)
  | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
  | Sum.inr (Sum.inr c) => Sum.inr c

lemma un_assoc {α β γ : Type} (s : (α ⊕ β) ⊕ γ)
  : unassoc (assoc s) = s
:= by
  cases s with
  | inl ab =>
    cases ab <;> rfl
  | inr c =>
    rfl

lemma assoc_un {α β γ : Type} (s : α ⊕ (β ⊕ γ))
  : assoc (unassoc s) = s
:= by
  cases s with
  | inl a =>
    rfl
  | inr bc =>
    cases bc <;> rfl

example (α β γ : Type) : (α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ) where
  toFun := assoc
  invFun := unassoc
  left_inv := by
    intro s
    exact un_assoc s
  right_inv := by
    intro s
    exact assoc_un s
/-


# Products and sums together

Show `α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)`.

-/
def distrib {α β γ : Type} :
  α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
  :=
  λ p ↦ match p.2 with
  | Sum.inl b => Sum.inl (p.1, b)
  | Sum.inr c => Sum.inr (p.1, c)

def factor {α β γ : Type} :
  (α × β) ⊕ (α × γ) → α × (β ⊕ γ)
  :=
  λ s ↦ match s with
  | Sum.inl p => (p.1, Sum.inl p.2)
  | Sum.inr p => (p.1, Sum.inr p.2)

lemma factor_distrib {α β γ : Type} (p : α × (β ⊕ γ))
  : factor (distrib p) = p
:= by
  cases p with
  | mk a s =>
    cases s <;> rfl

lemma distrib_factor {α β γ : Type} (s : (α × β) ⊕ (α × γ))
  : distrib (factor s) = s
:= by
  cases s with
  | inl p =>
    cases p
    rfl
  | inr p =>
    cases p
    rfl

example (α β γ : Type) : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)
  where
  toFun := distrib
  invFun := factor
  left_inv := by
    intro p
    exact factor_distrib p
  right_inv := by
    intro s
    exact distrib_factor s
/-


# Direct injectivity proofs on pairs

Swapping components of a pair is injective.
-/
def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

example (α β : Type)
  : Injective (λ p : α × β ↦ (p.2, p.1))
:= by
  intro ⟨a, b⟩ ⟨a', b'⟩ h
  cases h
  rfl

example (α β : Type)
  : Injective (λ p : α × β ↦ (p.2, p.1))
:= by
  intro ⟨a, b⟩ ⟨a', b'⟩ h
  grind
/-

Associating nested pairs to the right is injective.
-/
example (α β γ : Type)
  : Injective (fun p : (α × β) × γ ↦ (p.1.1, (p.1.2, p.2)))
:= by
  intro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩  h
  cases h
  rfl

example (α β γ : Type)
  : Injective (fun p : (α × β) × γ ↦ (p.1.1, (p.1.2, p.2)))
:= by
  intro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩  h
  grind
/-


# A uniqueness principle for pairing

If two functions into a product have equal first and second projections, then the functions are equal.
-/
example (α β γ : Type) (f g : α → β × γ)
  (h1 : (λ a ↦ (f a).1) = (λ a ↦ (g a).1))
  (h2 : (λ a ↦ (f a).2) = (λ a ↦ (g a).2))
  : f = g
:= by
  funext a
  rcases hf : f a with ⟨f1, f2⟩
  rcases hg : g a with ⟨g1, g2⟩
  have hl := calc
    f1
    _ = (f a).1 := by rw [hf]
    _ = (λ a ↦ (f a).1) a := by rfl
    _ = (λ a ↦ (g a).1) a := by rw [h1]
    _ = (g a).1 := by rfl
    _ = g1 := by rw [hg]
  have hr := calc
    f2
    _ = (f a).2 := by rw [hf]
    _ = (λ a ↦ (f a).2) a := by rfl
    _ = (λ a ↦ (g a).2) a := by rw [h2]
    _ = (g a).2 := by rfl
    _ = g2 := by rw [hg]
  rw [hl, hr]
