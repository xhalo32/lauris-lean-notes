import Mathlib
/-

# Mapping functions over products

-/
def map {α β γ δ : Type} (f : α → β) (g : γ → δ) :
  α × γ → β × δ := λ p ↦ (f p.1, g p.2)

example (α β γ δ : Type) (f : α → β) (g : γ → δ)
  (a : α) (c : γ)
  : map f g (a, c) = (f a, g c)
:= by
  rfl

example (α β : Type) (p : α × β)
  : map id id = (id : α × β → α × β)
:= by
  funext p
  cases p
  rfl

example (α β γ δ ε ζ : Type)
  (f₁ : α → β) (f₂ : β → γ)
  (g₁ : δ → ε) (g₂ : ε → ζ)
  : (map f₂ g₂) ∘ (map f₁ g₁) = map (f₂ ∘ f₁) (g₂ ∘ g₁)
:= by
  funext p
  cases p
  rfl
/-


# Injectivity of operations on pairs

Commuting components of prod is injective.
-/
def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

def swapProd (α β : Type) : α × β → β × α :=
  fun p ↦ (p.2, p.1)

example (α β : Type)
  : Injective (swapProd α β)
:= by
  intro ⟨a, b⟩ ⟨a', b'⟩ h
  cases h
  rfl
/-

Associating nested pairs to the right is injective.
-/
def assocProd (α β γ : Type) : (α × β) × γ → α × (β × γ) :=
  fun p ↦ (p.1.1, (p.1.2, p.2))

example (α β γ : Type)
  : Injective (assocProd α β γ)
:= by
  intro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩  h
  cases h
  rfl
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


# Mapping functions over sums

-/
def mapSum {α β γ δ : Type} (f : α → β) (g : γ → δ) :
  α ⊕ γ → β ⊕ δ
  :=
  λ s ↦ match s with
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr c => Sum.inr (g c)

example (α β γ δ : Type) (f : α → β) (g : γ → δ) (a : α)
  : mapSum f g (Sum.inl a) = Sum.inl (f a)
:= by
  rfl

example (α β γ δ : Type) (f : α → β) (g : γ → δ) (c : γ)
  : mapSum f g (Sum.inr c) = Sum.inr (g c)
:= by
  rfl

example (α β : Type)
  : mapSum id id = (id : α ⊕ β → α ⊕ β)
:= by
  funext s
  cases s <;> rfl

example (α β γ δ ε ζ : Type)
  (f₁ : α → β) (f₂ : β → γ)
  (g₁ : δ → ε) (g₂ : ε → ζ)
  : (mapSum f₂ g₂) ∘ (mapSum f₁ g₁)
    = mapSum (f₂ ∘ f₁) (g₂ ∘ g₁)
:= by
  funext s
  cases s <;> rfl
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
