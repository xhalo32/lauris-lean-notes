import Mathlib
/-

# Equivalence of types

Recall that currying, together with its inverse, establishes the equivalence `(α × β → γ) ≃ (α → β → γ)`. Here `≃` is syntactic sugar for a structure. Find this structure.
-/
variable (α β : Type)
set_option pp.notation false in
#reduce α ≃ β

example : (α ≃ β) = (Equiv α β) := rfl

#print Equiv
#print Function.LeftInverse
#print Function.RightInverse
/-

`Equiv` uses [default values][defaults] enabling the automation that we used earlier for currying among other things.

[defaults]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structure-fields

Write your own version of `Equiv` omitting the default values.
-/
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

structure Embedding (α β : Type) where
  toFun : α → β
  inj' : Injective toFun
/-


# Universal property of coproduct

`Sum` is a [coproduct][coproduct] in the sense that it satisfies the below universal property.

[coproduct]: https://en.wikipedia.org/wiki/Coproduct

Consider
-/
def injs {α β γ : Type} :
  (α ⊕ β → γ) → (α → γ) × (β → γ)
  :=
  λ f ↦ (λ a ↦ f (Sum.inl a), λ b ↦ f (Sum.inr b))
/-

Show that `injs` gives the equivalence
`(α ⊕ β → γ) ≃ (α → γ) × (β → γ)`.
-/
def uninjs {α β γ : Type} :
  (α → γ) × (β → γ) → (α ⊕ β → γ)
  :=
  λ p ↦ λ s ↦ match s with
  | Sum.inl a => p.1 a
  | Sum.inr b => p.2 b

example (α β γ : Type) : (α ⊕ β → γ) ≃ (α → γ) × (β → γ)
  where
  toFun := injs
  invFun := uninjs
  left_inv := by
    intro f
    funext s
    cases s <;> rfl
  right_inv := by
    intro p
    rfl
/-


# Sum as symmetric monoidal category

Like `Prod`, `Sum` forms a symmetric monoidal category.


## Symmetry

Consider the swap map
-/
def swap {α β : Type} (s : α ⊕ β) : β ⊕ α :=
  match s with
  | Sum.inl a => Sum.inr a
  | Sum.inr b => Sum.inl b
/-

Show that `swap` gives the equivalence
`α ⊕ β ≃ β ⊕ α`.
-/
-- __Solution__
lemma swap_swap {α β : Type} (s : α ⊕ β)
  : swap (swap s) = s
:= by
  cases s with
  | inl a => rfl
  | inr b => rfl

def braiding {α β : Type} : α ⊕ β ≃ β ⊕ α where
  toFun := swap
  invFun := swap
  left_inv := by
    intro s
    exact swap_swap s
  right_inv := by
    intro s
    exact swap_swap s

-- Here are some variations of `swap_swap`.
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


## Associativity

Consider
-/
def assoc {α β γ : Type} :
  (α ⊕ β) ⊕ γ → α ⊕ (β ⊕ γ)
  :=
  λ s ↦ match s with
  | Sum.inl (Sum.inl a) => Sum.inl a
  | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
  | Sum.inr c           => Sum.inr (Sum.inr c)
/-

Show that `assoc` gives the equivalence
`(α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ)`.
-/
def unassoc {α β γ : Type} :
  α ⊕ (β ⊕ γ) → (α ⊕ β) ⊕ γ
  :=
  λ s ↦ match s with
  | Sum.inl a           => Sum.inl (Sum.inl a)
  | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
  | Sum.inr (Sum.inr c) => Sum.inr c

def sum_associator {α β γ : Type} :
  (α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ)
where
  toFun := assoc
  invFun := unassoc
  left_inv := by
    intro s
    cases s with
    | inl ab => cases ab <;> rfl
    | inr c => rfl
  right_inv := by
    -- __Solution__
    intro s
    cases s with
    | inl a => rfl
    | inr bc => cases bc <;> rfl
/-

Here is a variation of `left_inv`.
-/
example (α β γ : Type) (s : (α ⊕ β) ⊕ γ)
  : unassoc (assoc s) = s
:= by
  obtain ((_ | _) | _) := s <;> rfl
/-


## Unit

`Empty` is the canonical type with no elements. It is the monoidal unit for `Sum`.

Show `Empty ⊕ α ≃ α`.
-/
def leftUnitor {α : Type} : Empty ⊕ α ≃ α where
  toFun :=
    λ s ↦ match s with
    | Sum.inl e => e.elim
    | Sum.inr a => a
  invFun := λ a ↦ Sum.inr a
  left_inv := by
    intro s
    cases s with
    | inl e => exact e.elim
    | inr a => rfl
/-
Observe that the default value works for `right_inv`.

Show `α ⊕ Empty ≃ α`.
-/
-- __Solution__
def rightUnitor {α : Type} : α ⊕ Empty ≃ α where
  toFun :=
    λ s ↦ match s with
    | Sum.inl a => a
    | Sum.inr e => e.elim
  invFun := λ a ↦ Sum.inl a
  left_inv := by
    intro s
    cases s with
    | inl a => rfl
    | inr e => exact e.elim
/-


# Product and sum as distributive category

`Prod` and `Sum` form a [distributive category](https://en.wikipedia.org/wiki/Distributive_category).

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

def prod_sum_distrib {α β γ : Type} :
  α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)
  where
  toFun := distrib
  invFun := factor
  left_inv := by
    intro ⟨a, s⟩
    cases s <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl

-- Here is a variation of `left_inv`
example (α β γ : Type) (p : α × (β ⊕ γ))
  : factor (distrib p) = p
:= by
  obtain ⟨_, (_ | _)⟩ := p <;> rfl

-- Here is a variation of `right_inv`
example (α β γ : Type) (s : (α × β) ⊕ (α × γ))
  : distrib (factor s) = s
:= by
  obtain (⟨_, _⟩ | ⟨_, _⟩) := s <;> rfl
/-


# Further remarks

We can show that `Sum`, `Empty`, and
-/
def tensorHom {α β γ δ : Type}
  (f : α → γ) (g : β → δ) (s : α ⊕ β) : γ ⊕ δ :=
  match s with
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr b => Sum.inr (g b)
/-
form a `MonoidalCategory`.
-/
-- This is more of a remark than a problem, but it depends on the solutions above.
-- __Solution__
def whiskerLeft {α β δ : Type}
  (g : β → δ) := tensorHom (id : α → α) g

def whiskerRight {α β γ : Type}
  (f : α → γ) := tensorHom f (id : β → β)

instance : CategoryTheory.MonoidalCategory Type where
  tensorObj := Sum
  tensorUnit := Empty
  tensorHom := tensorHom
  whiskerLeft _ _ _ := whiskerLeft
  whiskerRight f _ := whiskerRight f
  associator _ _ _ := sum_associator.toIso
  leftUnitor _ := leftUnitor.toIso
  rightUnitor _ := rightUnitor.toIso
/-

In order to show that this category is symmetric, we need to provide several properties that the automation fails to prove.
-/
-- This is more of a remark than a problem, but it depends on the solutions above.
-- __Solution__
instance : CategoryTheory.SymmetricCategory Type where
  braiding _ _ := braiding.toIso
  braiding_naturality_left _ _ := by
    funext s
    cases s <;> rfl
  braiding_naturality_right _ _ := by
    intros
    funext s
    cases s <;> rfl
  hexagon_forward _ _ _ := by
    funext s
    obtain ((_ | _) | _) := s <;> rfl
  hexagon_reverse _ _ _ := by
    funext s
    obtain (_ | (_ | _)) := s <;> rfl
  symmetry _ _ := by
    funext s
    cases s <;> rfl
/-

We omit showing that `Prod` and `Sum` form
-/
#print CategoryTheory.IsMonoidalDistrib
/-
Showing this would require combining the monoidal structures of `Prod` and `Sum` and lies beyond our scope.
-/
