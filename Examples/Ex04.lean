import Mathlib
/-

# Implication

Modus ponens in tactic style.
-/
example (p q : Prop)
  (h1 : p → q)
  (h2 : p)
  : q
:= by
  apply h1
  exact h2

example (p q : Prop)
  : (p → q) → p → q
:= by
  intro hpq hp
  apply hpq
  exact hp

example (p q : Prop)
  : (p → q) → p → q
:= by grind
/-

Identity
-/
example (p : Prop)
  : p → p
:= by
  intro hp
  exact hp

example (p : Prop)
  : p → p
:= by grind
/-

Composition of implications
-/
example (p q r : Prop)
  (h1 : p → q)
  (h2 : q → r)
  : p → r
:= by
  intro hp
  apply h2
  apply h1
  exact hp

example (p q r : Prop)
  (h1 : p → q)
  (h2 : q → r)
  : p → r
:= by grind
/-

Weakening (ignoring assumptions)
-/
example (p q r : Prop)
  : (p → r) → (p → q → r)
:= by
  intro h hp _
  apply h
  exact hp

example (p q r : Prop)
  : (p → r) → (p → q → r)
:= by grind
/-

Repeating premise
-/
example (p q : Prop)
  (h : p → p → q)
  : p → q
:= by
  intro hp
  apply h
  -- We need to prove `p` twice
  · exact hp
  · exact hp

example (p q : Prop)
  (h : p → p → q)
  : p → q
:= by grind
/-

Reordering arguments
-/
example (p q r : Prop)
  : (p → q → r) → (q → p → r)
:= by
  intro h hq hp
  apply h
  -- We need to prove `p` and `q`
  · exact hp
  · exact hq

example (p q r : Prop)
  : (p → q → r) → (q → p → r)
:= by grind
/-

Higher-order implication
-/
example (p q : Prop)
  : (p → q) → (p → q)
:= by
  intro h hp
  apply h
  exact hp

example (p q : Prop)
  : (p → q) → (p → q)
:= by grind
/-


# Universal quantification

Identity
-/
example (α : Type) (P : α → Prop)
  : (∀ x, P x) → ∀ x, P x
:= by
  intro h x
  exact h x

example (α : Type) (P : α → Prop)
  : (∀ x, P x) → ∀ x, P x
:= by grind
/-

Application
-/
example (α : Type) (P : α → Prop) (a : α)
  (h : ∀ x, P x)
  : P a
:= by
  exact h a

example (α : Type) (P : α → Prop) (a : α)
  (h : ∀ x, P x)
  : P a
:= by grind
/-

Weakening
-/
example (α : Type) (P Q : α → Prop)
  (h : ∀ x, P x)
  : ∀ x, Q x → P x
:= by
  intro x _
  exact h x

example (α : Type) (P Q : α → Prop)
  (h : ∀ x, P x)
  : ∀ x, Q x → P x
:= by grind
/-

Reordering quantifiers
-/
example (α β : Type) (P : α → β → Prop)
  : (∀ x y, P x y) → (∀ y x, P x y)
:= by
  intro h y x
  exact h x y

example (α β : Type) (P : α → β → Prop)
  : (∀ x y, P x y) → (∀ y x, P x y)
:= by grind
/-

Composition under ∀
-/
example (α : Type) (P Q R : α → Prop)
  (h1 : ∀ x, P x → Q x)
  (h2 : ∀ x, Q x → R x)
  : ∀ x, P x → R x
:= by
  intro x hp
  apply h2
  apply h1
  exact hp

example (α : Type) (P Q R : α → Prop)
  (h1 : ∀ x, P x → Q x)
  (h2 : ∀ x, Q x → R x)
  : ∀ x, P x → R x
:= by grind
/-

Distributing implication over ∀
-/
example (α : Type) (P Q : α → Prop)
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x)
:= by
  intro hp x
  apply h
  exact hp x

example (α : Type) (P Q : α → Prop)
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x)
:= by grind
/-

Constant proof
-/
example (α : Type) (P : Prop) :
  P → ∀ x : α, P
:= by
  intro hp x
  exact hp

example (α : Type) (P : Prop) :
  P → ∀ x : α, P
:= by grind
/-

Pointwise composition
-/
example (α : Type) (P Q R : α → Prop) (x : α)
  (h1 : ∀ x, P x → Q x)
  (h2 : ∀ x, Q x → R x)
  (hp : P x)
  : R x
:= by
  apply h2
  apply h1
  exact hp

example (α : Type) (P Q R : α → Prop) (x : α)
  (h1 : ∀ x, P x → Q x)
  (h2 : ∀ x, Q x → R x)
  (hp : P x)
  : R x
:= by grind
/-


# Injectivity

Definition of injectivity
-/
def Injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y
/-

The identity function is injective.
-/
example (α : Type) : Injective (id : α → α) := by
  intro x y h
  exact h
/-

A constant function is injective only if the domain has at most one element.
-/
example (α β : Type) (b : β)
  (h : Injective (λ _ : α ↦ b))
  : ∀ x y : α, x = y
:= by
  intro a a'
  apply h
  rfl
/-

Injectivity enables cancellation on the left.
-/
example (α β : Type) (f : α → β) (a a' : α)
  (hf : Injective f)
  (h : f a = f a')
  : a = a'
:= by
  apply hf
  exact h
/-

The composition of two injective functions is injective.
-/
example (α β γ : Type) (f : α → β) (g : β → γ)
  (hf : Injective f) (hg : Injective g)
  : Injective (g ∘ f)
:= by
  intro a a' h
  apply hf
  apply hg
  exact h
/-

A function with a left inverse is injective.
-/
example (α β : Type) (f : α → β) (l : β → α)
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
/-

If `g ∘ f` is injective, then `f` is injective.
-/
example (α β γ : Type) (f : α → β) (g : β → γ)
  (h : Injective (g ∘ f))
  : Injective f
:= by
  intro a a' hfa
  apply h
  calc
    (g ∘ f) a
    _ = g (f a) := by rfl
    _ = g (f a') := by rw [hfa]
    _ = (g ∘ f) a' := by rfl
/-

If functions are equal after composition with an injective map, then they are equal.
-/
example (α β γ : Type) (f g : α → β) (h : β → γ)
  (hh : Injective h)
  (hfg : h ∘ f = h ∘ g)
  : f = g
:= by
  funext a
  apply hh
  calc
    h (f a)
    _ = (h ∘ f) a := by rfl
    _ = (h ∘ g) a := by rw [hfg]
    _ = h (g a) := by rfl
