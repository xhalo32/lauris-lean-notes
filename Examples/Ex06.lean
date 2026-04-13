import Mathlib
/-

# Equivalence

Like `And`, equivalence `p ↔ q` is a structure. Find this structure and write your own version of it.
-/
-- __Solution__
namespace Demo
variable (p q : Prop)
set_option pp.notation false in
#reduce p ↔ q
end Demo

example (p q : Prop) : (p ↔ q) = (Iff p q) := rfl

#print Iff

structure Iff' (p q : Prop) : Prop where
  mp : p → q
  mpr : q → p
/-

The definition of `↔` encodes [biconditional introduction][bicond-intro].

[bicond-intro]: https://en.wikipedia.org/wiki/Biconditional_introduction
-/
example (p q : Prop) (h1 : p → q) (h2 : q → p) : p ↔ q
:= by
  constructor
  · exact h1
  · exact h2
/-

Formulate and prove [biconditional elimination][bicond-elim] for `Iff'`.

[bicond-elim]: https://en.wikipedia.org/wiki/Biconditional_elimination
-/
-- __Solution__
example (h : Iff' p q) : p → q
:= by
  obtain ⟨hpq, _⟩ := h
  exact hpq

example (h : Iff' p q) : q → p
:= by
  obtain ⟨_, hqp⟩ := h
  exact hqp
/-


# Logical equivalence as equivalence of types

The two equivalences `p ≃ q` and `p ↔ q` coincide in the following sense.
-/
example (p q : Prop) (e : p ≃ q) : p ↔ q
:= by
  constructor
  · exact e.toFun
  · exact e.invFun

def iff_equiv (p q : Prop) (h : p ↔ q) : p ≃ q where
  toFun := h.mp
  invFun := h.mpr

set_option pp.proofs true in
#print iff_equiv
/-

Propositions `left_inv` and `right_inv` are proven by their default values. To understand this, let `hpq : p → q` and `hqp : q → p`, and show that `hqp` is the inverse of `hpq` due to proof irrelevance (all proofs of the same proposition are equal).
-/
example (p q : Prop) (hpq : p → q) (hqp : q → p)
  : ∀ (π : p), hqp (hpq π) = π
:= by
  intro π
  rfl

example (p q : Prop) (hpq : p → q) (hqp : q → p)
  : ∀ (π : q), hpq (hqp π) = π
:= by
  intro π
  rfl
/-


# Logical implication as embedding of types

Show that `p ↪ q` and `p → q` coincide.
-/
-- __Solution__
example (p q : Prop) (e : p ↪ q) : p → q
:= by
  exact e.toFun

example (p q : Prop) (h : p → q) : p ↪ q where
  toFun := h
  inj' := by
    intro π₁ π₂ _
    rfl
/-


# Conjunction and disjunction as product and coproduct

`And` and `Or` are the analogues of `Prod` and `Sum` acting on `Prop` rather than on `Type`.

All examples in this section can be solved by `grind`, but you may still want to write them out step by step for practice.


## Universal property of product

Show the universal property of `And` as a product.
-/
example (p q r : Prop)
  : (p → q ∧ r) ↔ ((p → q) ∧ (p → r))
:= by
  -- __Solution__
  constructor
  · intro h
    constructor
    · intro hp
      obtain ⟨hq, _⟩ := h hp
      exact hq
    · intro hp
      obtain ⟨_, hq⟩ := h hp
      exact hq
  · intro h
    obtain ⟨hpq, hpr⟩ := h
    intro hp
    exact ⟨hpq hp, hpr hp⟩
/-


## Universal property of coproduct

Show the universal property of `Or` as a coproduct.
-/
example (p q r : Prop)
  : (p ∨ q → r) ↔ ((p → r) ∧ (q → r))
:= by
  -- __Solution__
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro h
    obtain ⟨hpr, hqr⟩ := h
    intro hpq
    obtain (hp | hq) := hpq
    · exact hpr hp
    · exact hqr hq
/-


## Conjunction as symmetric monoidal category

Like `Prod`, `And` forms a symmetric monoidal category. Since `MonoidalCategory`  applies to types rather than propositions, we cannot declare `And` its instance.

Show the symmetry
-/
example (p q : Prop)
  : p ∧ q ↔ q ∧ p
:= by
  -- __Solution__
  constructor
  · intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩
/-

Show the associativity
-/
example (p q r : Prop)
  : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
:= by
  -- __Solution__
  constructor
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, ⟨hq, hr⟩⟩
  · intro ⟨hp, ⟨hq, hr⟩⟩
    exact ⟨⟨hp, hq⟩, hr⟩
/-

`True` is the monoidal unit for `And`.

Show
-/
example (p : Prop)
  : p ∧ True ↔ p
:= by
  -- __Solution__
  constructor
  · intro ⟨hp, _⟩
    exact hp
  · intro hp
    exact ⟨hp, ⟨⟩⟩
/-

Show
-/
example (p : Prop)
  : True ∧ p ↔ p
:= by
  -- __Solution__
  constructor
  · intro ⟨_, hp⟩
    exact hp
  · intro hp
    exact ⟨⟨⟩, hp⟩
/-


## Disjunction as symmetric monoidal category

Like `Sum`, `Or` forms a symmetric monoidal category.

Show the symmetry
-/
example (p q : Prop)
  : p ∨ q ↔ q ∨ p
:= by
  constructor
  · intro h
    obtain (hp | hq) := h
    · right
      exact hp
    · left
      exact hq
  · intro h
    obtain (hq | hp) := h
    · right
      exact hq
    · left
      exact hp

-- An alternative solution using tactic combinators
example (p q : Prop)
  : p ∨ q ↔ q ∨ p
:= by
  constructor <;> intro h <;> obtain (h | h) := h <;>
  solve
  | left
    exact h
  | right
    exact h
/-

Show the associativity
-/
example (p q r : Prop)
  : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
:= by
  -- __Solution__
  constructor
  · intro h
    obtain ((hp | hq) | hr) := h
    · left
      exact hp
    · right
      left
      exact hq
    · right
      right
      exact hr
  · intro h
    obtain (hp | (hq | hr)) := h
    · left
      left
      exact hp
    · left
      right
      exact hq
    · right
      exact hr

-- __Solution__ using tactic combinators
example (p q r : Prop)
  : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
:= by
  constructor <;> intro h <;>
  (repeat' obtain (h | h) := h) <;>
  solve
  | repeat left
    exact h
  | repeat right
    exact h
  | left
    right
    exact h
  | right
    left
    exact h
/-

`False` is the monoidal unit for `Or`.

Show
-/
example (p : Prop)
  : p ∨ False ↔ p
:= by
  -- __Solution__
  constructor
  · intro h
    obtain (hp | hf) := h
    · exact hp
    · exact hf.elim
  · intro hp
    left
    exact hp
/-

Show
-/
example (p : Prop)
  : False ∨ p ↔ p
:= by
  -- __Solution__
  constructor
  · intro h
    obtain (hf | hp) := h
    · exact hf.elim
    · exact hp
  · intro hp
    right
    exact hp
/-


## Conjuction and disjunction as distributive category

Like `Prod` and `Sum`, `And` and `Or` form a distributive category.

Show
-/
example (p q r : Prop)
  : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
:= by
  -- __Solution__
  constructor
  · intro h
    obtain ⟨hp, (hq | hr)⟩ := h
    · left
      exact ⟨hp, hq⟩
    · right
      exact ⟨hp, hr⟩
  · intro h
    obtain (⟨hp, hq⟩ | ⟨hp, hr⟩) := h
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩
/-


# Injectivity and surjectivity

Definition of surjectivity
-/
#print Function.Surjective

open Function in
example (α β : Type) (f : α → β) :
  Surjective f = (∀ b : β, ∃ a : α, f a = b) := rfl
/-


## Positive results on surjectivity

Recall that we studied earlier the following example.
-/
open Function in
example (α β γ : Type) (f : α → β) (g : β → γ)
  (hf : Injective f) (hg : Injective g)
  : Injective (g ∘ f)
:= by exact Injective.comp hg hf
/-
Here the proof is simply using a lemma in Mathlib. To search for a lemma, use `exact?`.

Show the analogous statement on surjectivity.
-/
open Function in
example (α β γ : Type) (f : α → β) (g : β → γ)
  (hf : Surjective f) (hg : Surjective g)
  : Surjective (g ∘ f)
:= by
  intro c
  obtain ⟨b, hb⟩ := hg c
  obtain ⟨a, ha⟩ := hf b
  use a
  simp [ha, hb]
/-

Show the analogue of
-/
open Function in
example (α β γ : Type) (f : α → β) (g : β → γ)
  (h : Injective (g ∘ f))
  : Injective f
:= by exact Injective.of_comp h

open Function in
example (α β γ : Type) (f : α → β) (g : β → γ)
  (h : Surjective (g ∘ f))
  : Surjective g
:= by
  -- __Solution__
  intro b
  obtain ⟨a, ha⟩ := h b
  use f a
  simp at ha
  exact ha
/-


## Counterexamples

`Bool` is a canonical type with two elements called `false` and `true`. These should not be confused with the propositions `False` and `True`.
-/
#print Bool
/-

Consider the functions
-/
def f (x : Unit) : Bool := false

def g (x : Bool) : Unit :=
  match x with
  | false => ⟨⟩
  | true => ⟨⟩
/-

The composition `f ∘ g` is injective and surjective.
-/
open Function in
example : Injective (g ∘ f)
:= by
  simp [Injective]

open Function in
example : Surjective (g ∘ f)
:= by
  -- __Solution__
  simp [Surjective]
/-

However, `g` is not injective and `f` is not surjective.
-/
open Function in
example : ¬Injective g := by
  -- __Solution__
  simp [Injective]

open Function in
example : ¬Surjective f := by
  -- __Solution__
  simp [Surjective, f]
/-


# Boolean algebra

[Boolean algebra][boolean-algebra] uses three operators that correspond to negation, conjunction and disjunction.

[boolean-algebra]: https://en.wikipedia.org/wiki/Boolean_algebra

`Bool` is embedded in `ℕ`.
-/
example : false = 0 := rfl
example : true = 1 := rfl
/-

Show that the three operators `!`, `&&`, and `||` can be written in terms of arithmetic operators in `ℕ`.
-/
example (x : Bool) : !x = 1 - x
:= by
  cases x <;> rfl

example (x y : Bool) : (x && y) = x * y
:= by
  -- __Solution__
  rfl

example (x y : Bool) : (x || y) = x + y - x * y
:= by
  -- __Solution__
  cases x <;> cases y <;> rfl
/-


## Truth tables

Form the truth table of negation.
-/
example : !0 = 1 := rfl
example : !1 = 0 := rfl
/-

Form the truth table of conjunction.
-/
-- __Solution__
example : (0 && 0) = 0 := rfl
example : (0 && 1) = 0 := rfl
example : (1 && 0) = 0 := rfl
example : (1 && 1) = 1 := rfl
/-

Form the truth table of disjunction.
-/
-- __Solution__
example : (0 || 0) = 0 := rfl
example : (0 || 1) = 1 := rfl
example : (1 || 0) = 1 := rfl
example : (1 || 1) = 1 := rfl
/-


## Classical logic

Propositions can be mapped to Booleans according to their truth value. However, this cannot be done constructively, since the [law of excluded middle][excluded-middle] is required. We will give more detail later and simply use the truth preserving function `decide` from `Prop` to `Bool`. Non-constructive functions must be labeled with `noncomputable`.

[excluded-middle]: https://en.wikipedia.org/wiki/Law_of_excluded_middle

-/
noncomputable def decide' : Prop → Bool := by
  intro p
  classical
  exact decide p

example (p : Prop)
  : decide' p = true ↔ p
:= by
  by_cases hp : p <;> simp [decide']
/-

Show that `decide'` is a Boolean algebra homomorphism.
-/
example (p : Prop)
  : decide' (¬p) = !(decide' p)
:= by
  by_cases hp : p <;> simp [decide']

example (p q : Prop)
  : decide' (p ∧ q) = (decide' p && decide' q)
:= by
  by_cases hp : p <;> by_cases hq : q <;>
  simp [decide', hp]

example (p q : Prop)
  : decide' (p ∨ q) = (decide' p || decide' q)
:= by
  -- __Solution__
  by_cases hp : p <;> by_cases hq : q <;>
  simp [decide', hp]
/-


## Fixed points of Boolean functions

Show that every Boolean function, except negation, has a fixed point.
-/
example (f : Bool → Bool)
  : f = (λ x ↦ !x) ∨ ∃ x : Bool, f x = x
:= by
  cases h1 : f false <;> cases h2 : f true <;>
  -- __Solution__
  solve
  | left
    funext x
    cases x
    · exact h1
    · exact h2
  | right
    use true
  | right
    use false
/-


# Fixed points of trilean involutions

Consider a type with three elements.
-/
inductive Trilean where | F | U | T
/-

Show that every trilean involution has a fixed point.

Hint: `grind` can do a lot work.

-/
open Trilean in
example (f : Trilean → Trilean)
  (h : ∀ x : Trilean, f (f x) = x)
  : ∃ x : Trilean, f x = x
:= by
  -- __Solution__
  cases _ : f F <;> cases _ : f U <;> cases _ : f T <;>
  grind
