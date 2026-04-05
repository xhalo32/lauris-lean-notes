import Mathlib
/-

# Equivalence of types

Recall that currying, together with its inverse, establishes the equivalence `(α × β → γ) ≃ (α → β → γ)`. Here `≃` is syntactic sugar for a structure. Find this structure and write your own version of it.
-/
variable (α β : Type)
set_option pp.notation false in
#reduce α ≃ β

example : (α ≃ β) = (Equiv α β) := rfl

#print Equiv
#print Function.LeftInverse
#print Function.RightInverse

-- Equiv uses [default values](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structure-fields)
-- We omit default values in our versions

-- A version unpacking `left_inv` and `right_inv`
structure Equiv' (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ (a : α), invFun (toFun a) = a
  right_inv : ∀ (b : β), toFun (invFun b) = b

-- A version using our own `LeftInverse` and `RightInverse`
def LeftInverse {α β : Type}
  (l : β → α) (f : α → β) : Prop :=
  ∀ (x : α), l (f x) = x

def RightInverse {α β : Type}
  (r : β → α) (f : α → β) : Prop :=
  LeftInverse f r

structure Equiv'' (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : LeftInverse invFun toFun
  right_inv : RightInverse invFun toFun
/-


# Embedding of types

Embedding of types is written as `α ↪ β`. Here `↪` is syntactic sugar for a structure. Find this structure and write your own version of it using `Injective`.
-/
def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

-- __Solution__
set_option pp.notation false in
#reduce α ↪ β

example : (α ↪ β) = (Function.Embedding α β) := rfl

#print Function.Embedding
#print Function.Injective

structure Embedding' (α β : Type) where
  toFun : α → β
  inj' : Injective toFun
/-

Equivalence `α ≃ β` gives `α ↪ β`.
-/
-- Recall our earlier proof
lemma left_inv_inj {α β : Type} (f : α → β) (l : β → α)
  (h : l ∘ f = id)
  : Injective f
:= by
  intro a a' hf
  calc
    a
    _ = id a := by rfl
    _ = (l ∘ f) a := by rw [h]
    _ = l (f a) := by rfl
    _ = l (f a') := by rw [hf]
    _ = (l ∘ f) a' := by rfl
    _ = id a' := by rw [h]
    _ = a' := by rfl

example (α β : Type)
  (e : α ≃ β)
  : α ↪ β
where
  toFun := e.toFun
  inj'  := by
    apply left_inv_inj e.toFun e.invFun
    funext a
    calc
      (e.invFun ∘ e.toFun) a
      _ = e.invFun (e.toFun a) := by rfl
      _ = a := by rw [e.left_inv]
      _ = id a := by rfl
/-

Show that `α ≃ β` gives `β ↪ α`.
-/
example (α β : Type)
  (e : α ≃ β)
  : β ↪ α
where
  toFun := e.invFun
  inj'  := by
    -- __Solution__
    apply left_inv_inj e.invFun e.toFun
    funext b
    calc
      (e.toFun ∘ e.invFun) b
      _ = e.toFun (e.invFun b) := by rfl
      _ = b := by rw [e.right_inv]
      _ = id b := by rfl
/-


# Components of sum

Show `α ⊕ β ≃ β ⊕ α`.
-/
def swap {α β : Type} (s : α ⊕ β) : β ⊕ α :=
  match s with
  | Sum.inl a => Sum.inr a
  | Sum.inr b => Sum.inl b

lemma swap_swap {α β : Type} (s : α ⊕ β)
  : swap (swap s) = s
:= by
  cases s with
  | inl a => rfl
  | inr b => rfl

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

Here are some variations of `swap_swap`.
-/
example (α β : Type) (s : α ⊕ β)
  : swap (swap s) = s
:= by
  cases s with
  | inl => rfl
  | inr => rfl

example (α β : Type) (s : α ⊕ β)
  : swap (swap s) = s
:= by
  cases s
  · rfl
  · rfl

example (α β : Type) (s : α ⊕ β)
  : swap (swap s) = s
:= by
  cases s <;> rfl

example (α β : Type) (s : α ⊕ β)
  : swap (swap s) = s
:= by
  obtain (a | b) := s
  · rfl
  · rfl
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
  -- __Solution__
  cases s with
  | inl a =>
    rfl
  | inr bc =>
    cases bc <;> rfl

-- __Solution__ packaging into `≃`
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

Here is a variation of `un_assoc`.
-/
example (α β γ : Type) (s : (α ⊕ β) ⊕ γ)
  : unassoc (assoc s) = s
:= by
  obtain ((a | b) | c) := s
  · rfl
  · rfl
  . rfl
/-

# Products and sums together

Show `α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)`.
-/
-- __Solution__
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

-- Here is a variation of `factor_distrib`
example (α β γ : Type) (p : α × (β ⊕ γ))
  : factor (distrib p) = p
:= by
  obtain ⟨a, (b | c)⟩ := p
  · rfl
  · rfl

-- Here is a variation of `distrib_factor`
example (α β γ : Type) (s : (α × β) ⊕ (α × γ))
  : distrib (factor s) = s
:= by
  obtain (⟨a, b⟩ | ⟨a, c⟩) := s
  · rfl
  · rfl
/-


# Function from a sum

Function from a disjoint union is determined by its restrictions.
-/
example (α β γ : Type) (f g : α ⊕ β → γ) (x : α ⊕ β)
  (hl : ∀ a, f (Sum.inl a) = g (Sum.inl a))
  (hr : ∀ b, f (Sum.inr b) = g (Sum.inr b))
  : f x = g x
:= by
  obtain (a | b) := x
  · -- 1st case x = a : α
    -- __Solution__
    exact hl a
  · -- 2nd case x = b : β
    -- __Solution__
    exact hr b

-- __Solution__ using grind
example (α β γ : Type) (f g : α ⊕ β → γ) (x : α ⊕ β)
  (hl : ∀ a, f (Sum.inl a) = g (Sum.inl a))
  (hr : ∀ b, f (Sum.inr b) = g (Sum.inr b))
  : f x = g x
:= by
  grind
/-

A slightly harder variant.
-/
example (α β γ : Type) (f g : α ⊕ β → γ)
  (hl : (λ a ↦ f (Sum.inl a)) = (λ a ↦ g (Sum.inl a)))
  (hr : (λ b ↦ f (Sum.inr b)) = (λ b ↦ g (Sum.inr b)))
  : f = g
:= by
  -- __Solution__
  funext x
  obtain (a | b) := x
  · calc
    f (Sum.inl a)
    _ = (λ a ↦ f (Sum.inl a)) a := by rfl
    _ = (λ a ↦ g (Sum.inl a)) a := by rw [hl]
    _ = g (Sum.inl a) := by rfl
  · calc
    f (Sum.inr b)
    _ = (λ b ↦ f (Sum.inr b)) b := by rfl
    _ = (λ b ↦ g (Sum.inr b)) b := by rw [hr]
    _ = g (Sum.inr b) := by rfl
/-


# Pairs and equality

Extensionality of pairs.
-/
lemma prod_ext {α β : Type} {p q : α × β}
  (h1 : p.1 = q.1)
  (h2 : p.2 = q.2)
  : p = q
:= by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  cases h1
  cases h2
  rfl

example (α β : Type) (p q : α × β)
  (h1 : p.1 = q.1)
  (h2 : p.2 = q.2)
  : p = q
:= by
  grind
/-

Equality of pairs implies equality of components.
-/
example (α β : Type) (p q : α × β)
  (h : p = q)
  : p.1 = q.1
:= by
  -- __Solution__
  cases h
  rfl

-- __Solution__ by grind
example (α β : Type) (p q : α × β)
  (h : p = q)
  : p.1 = q.1
:= by
  grind
/-


# Function to a product

Function to a product is determined by its components.
-/
example (α β γ : Type) (f g : α → β × γ) (a : α)
  (h1 : ∀ a, (f a).1 = (g a).1)
  (h2 : ∀ a, (f a).2 = (g a).2)
  : f a = g a
:= by
  apply prod_ext
  · -- 1st case/component
    -- __Solution__
    exact h1 a
  · -- 2nd case/component
    -- __Solution__
    exact h2 a

-- __Solution__ using grind
example (α β γ : Type) (f g : α → β × γ) (a : α)
  (h1 : ∀ a, (f a).1 = (g a).1)
  (h2 : ∀ a, (f a).2 = (g a).2)
  : f a = g a
:= by
  grind
/-

A slightly harder variant.
-/
example (α β γ : Type) (f g : α → β × γ)
  (h1 : (λ a ↦ (f a).1) = (λ a ↦ (g a).1))
  (h2 : (λ a ↦ (f a).2) = (λ a ↦ (g a).2))
  : f = g
:= by
  funext a
  apply prod_ext
  · -- 1st case/component
    -- __Solution__
    calc
    (f a).1
    _ = (λ a ↦ (f a).1) a := by rfl
    _ = (λ a ↦ (g a).1) a := by rw [h1]
    _ = (g a).1 := by rfl
  · -- 2nd case/component
    -- __Solution__
    calc
    (f a).2
    _ = (λ a ↦ (f a).2) a := by rfl
    _ = (λ a ↦ (g a).2) a := by rw [h2]
    _ = (g a).2 := by rfl
