import Mathlib
/-

# Equivalence

Like `And`, equivalence `p ↔ q` is a structure. Find this structure and write your own version of it.
-/
-- __Solution__
variable (p q : Prop)
set_option pp.notation false in
#reduce p ↔ q

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

-- An alternative solution by brute force
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

-- __Solution__ by brute force
example (p q r : Prop)
  : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
:= by
  constructor <;> intro h <;> (
    first
    | obtain ((h | h) | h) := h
    | obtain (h | (h | h)) := h
  ) <;>
  solve
  | left
    exact h
  | right
    exact h
  | left
    left
    exact h
  | left
    right
    exact h
  | right
    left
    exact h
  | right
    right
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
