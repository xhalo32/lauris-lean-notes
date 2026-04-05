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
  -- __Solution__
  have hr := calc
    f2
    _ = (f a).2 := by rw [hf]
    _ = (λ a ↦ (f a).2) a := by rfl
    _ = (λ a ↦ (g a).2) a := by rw [h2]
    _ = (g a).2 := by rfl
    _ = g2 := by rw [hg]
  rw [hl, hr]
