import Mathlib
/-

# Currying

[Currying][currying] is the technique of translating a function that takes a pair as its argument into a function whose codomain is a function type.

[currying]: https://en.wikipedia.org/wiki/Currying

Consider
-/
def curry {α β γ : Type} (f : α × β → γ) : α → β → γ :=
  λ a b ↦ f (a, b)
/-

Find an inverse of `curry` and show that it is indeed an inverse. Moreover, show that `curry` gives the equivalence
`(α × β → γ) ≃ (α → β → γ)`.
-/
def uncurry {α β γ : Type} (g : α → β → γ) : α × β → γ :=
  λ p ↦ g p.1 p.2

lemma uncurry_curry {α β γ : Type} (f : α × β → γ)
  : uncurry (curry f) = f
:= by
  rfl

lemma curry_uncurry {α β γ : Type} (g : α → β → γ)
  : curry (uncurry g) = g
:= by
  rfl

example (α β γ : Type) : (α × β → γ) ≃ (α → β → γ) where
  toFun := curry
  invFun := uncurry
  left_inv := by
    intro f
    exact uncurry_curry f
  right_inv := by
    intro f
    exact curry_uncurry f
/-


# Universal property of product

`Prod` is a [product][product] in the sense of category theory, that is, it satisfies the below universal property.

[product]: https://en.wikipedia.org/wiki/Product_(category_theory)

Consider
-/
def projs {α β γ : Type} :
  (α → β × γ) → (α → β) × (α → γ)
  :=
  λ f ↦ (λ a ↦ (f a).1, λ a ↦ (f a).2)
/-

Show that `projs` gives the equivalence
`(α → β × γ) ≃ (α → β) × (α → γ)`.
-/
-- __Solution__
def unprojs {α β γ : Type} :
  (α → β) × (α → γ) → (α → β × γ)
  :=
  λ p ↦ λ a ↦ (p.1 a, p.2 a)

example (α β γ : Type) : (α → β × γ) ≃ (α → β) × (α → γ) where
  toFun := projs
  invFun := unprojs
  left_inv := by
    intro f
    rfl
  right_inv := by
    intro p
    rfl
/-


# Product as symmetric monoidal category

Let us show that `Prod` forms a
[symmetric monoidal category](https://en.wikipedia.org/wiki/Symmetric_monoidal_category).


## Symmetry

Consider the swap map
-/
def swap {α β : Type} : α × β → β × α :=
  λ p ↦ (p.2, p.1)
/-

Show that `swap` gives the equivalence
`α × β ≃ β × α`.
-/
-- __Solution__
lemma swap_swap {α β : Type} (p : α × β)
  : swap (swap p) = p
:= by
  rfl

example (α β : Type) : α × β ≃ β × α where
  toFun := swap
  invFun := swap
  left_inv := by
    intro p
    exact swap_swap p
  right_inv := by
    intro p
    exact swap_swap p
/-


## Associativity

Consider
-/
def assoc {α β γ : Type} : (α × β) × γ → α × (β × γ) :=
  λ p ↦ (p.1.1, (p.1.2, p.2))
/-

Show that `assoc` gives the equivalence
`(α × β) × γ ≃ α × (β × γ)`.
-/
-- __Solution__
def unassoc {α β γ : Type} : α × (β × γ) → (α × β) × γ :=
  λ p ↦ ((p.1, p.2.1), p.2.2)

example (α β γ : Type) : (α × β) × γ ≃ α × (β × γ) where
  toFun := assoc
  invFun := unassoc
  left_inv := by
    intro p
    rfl
  right_inv := by
    intro p
    rfl
/-


## Unit

`Unit` is the canonical type with one element. It is the monoidal unit for `Prod`, and its unique element is written `()`.

Show `α × Unit ≃ α`.
-/
example (α : Type) : α × Unit ≃ α where
  toFun := λ p ↦ p.1
  invFun := λ a ↦ (a, ())
  left_inv := by
    intro a
    rfl
  right_inv := by
    intro a
    rfl
/-

Show `Unit × α ≃ α `.
-/
-- __Solution__
example (α : Type) : Unit × α ≃ α where
  toFun := λ p ↦ p.2
  invFun := λ a ↦ ((), a)
  left_inv := by
    intro a
    rfl
  right_inv := by
    intro a
    rfl
/-


# Function composition

Function composition `∘` is associative.
-/
example (α β γ : Type) (f : α → β) (g : β → γ) (a : α)
  : (g ∘ f) a = g (f a)
:= by
  rfl

example (α β γ δ : Type) (f : α → β) (g : β → γ) (h : γ → δ)
  : (h ∘ g) ∘ f = h ∘ (g ∘ f)
:= by
  rfl
/-

Function composition can be viewed as a binary operation on functions from a type to itself.
-/
example (α : Type) :
  (α → α) → (α → α) → (α → α) := λ f g ↦ f ∘ g
/-

Show that `(α → α, ∘)` forms a semigroup.
-/
instance (α : Type) : Semigroup (α → α) where
  mul := λ f g ↦ f ∘ g
  mul_assoc := by
    intro h g f
    rfl
/-


# Identity function

Identity function `id` has the following properties.
-/
example (α : Type) : id = λ x : α ↦ x := rfl

example (α β : Type) (f : α → β)
  : f ∘ id = f
:= by
  rfl

example (α β : Type) (f : α → β)
  : id ∘ f = f
:= by
  rfl
/-

Show that `(α → α, ∘, id)` forms a monoid.
-/
instance (α : Type) : Monoid (α → α) where
  one := id
  one_mul := by
    -- __Solution__
    intro f
    rfl
  mul_one := by
    -- __Solution__
    intro f
    rfl
/-


# Uniqueness of inverse function

-/
example (α β : Type) (f : α → β) (l r : β → α)
  (h1 : l ∘ f = id)
  (h2 : f ∘ r = id)
  : l = r
:=
by
  funext x
  calc
    l x
    _ = l (id x) := by rfl
    _ = l ((f ∘ r) x) := by rw [h2]
    _ = (l ∘ f) (r x) := by rfl
    _ = id (r x) := by rw [h1]
    _ = r x := by rfl
/-


# Uniqueness of identity function

Left uniqueness
-/
example (α : Type) (e : α → α)
  (h : e ∘ id = id)
  : e = id
:= by
  -- __Solution__
  calc
    e = e ∘ id := by rfl
    _ = id := by rw [h]
/-

Right uniqueness
-/
example (α : Type) (e : α → α)
  (h : id ∘ e = id)
  : e = id
:= by
  -- __Solution__
  calc
    e = id ∘ e := by rfl
    _ = id := by rw [h]
/-


# Cancellation from an inverse

A left inverse gives left cancellation.
-/
example (α β : Type) (f : α → β) (l : β → α) (x y : α)
  (h1 : l ∘ f = id)
  (h2 : f x = f y)
  : x = y
:= by
  -- __Solution__
  calc
    x = id x := by rfl
    _ = (l ∘ f) x := by rw [h1]
    _ = l (f x) := by rfl
    _ = l (f y) := by rw [h2]
    _ = (l ∘ f) y := by rfl
    _ = id y := by rw [h1]
    _ = y := by rfl
