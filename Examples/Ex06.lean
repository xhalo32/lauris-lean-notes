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

example (p q : Prop) (h1 : p → q) (h2 : q → p) : p ↔ q
:= by
  grind
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


# Universal property of product

Show the universal property of `And` as a product in sense of category theory.
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

-- __Solution__ by grind
example (p q r : Prop)
  : (p → q ∧ r) ↔ ((p → q) ∧ (p → r))
:= by grind
/-


# Universal property of coproduct

Show the universal property of `Or` as a coproduct in sense of category theory.
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

-- __Solution__ by grind
example (p q r : Prop)
  : (p ∨ q → r) ↔ ((p → r) ∧ (q → r))
:= by
  grind
/-


# Conjunction as symmetric monoidal category

Like `Prod`, `And` forms a symmetric monoidal category.

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

-- __Solution__ by grind
example (p q : Prop)
  : p ∧ q ↔ q ∧ p
:= by grind
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

-- __Solution__ by grind
example (p q r : Prop)
  : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
:= by grind
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

-- __Solution__ by grind
example (p : Prop)
  : p ∧ True ↔ p
:= by grind
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

-- __Solution__ by grind
example (p : Prop)
  : True ∧ p ↔ p
:= by grind
/-


# Disjunction as symmetric monoidal category

Like `Sum`, `Or` forms a symmetric monoidal category.

Show the symmetry
-/
example (p q : Prop)
  : p ∨ q ↔ q ∨ p
:= by
  -- __Solution__
  constructor
  · intro h
    obtain (hp | hq) := h
    · exact Or.inr hp
    · exact Or.inl hq
  · intro h
    obtain (hq | hp) := h
    · exact Or.inr hq
    · exact Or.inl hp

-- __Solution__ by grind
example (p q : Prop)
  : p ∨ q ↔ q ∨ p
:= by grind
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
    · exact Or.inl hp
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr hr)
  · intro h
    obtain (hp | (hq | hr)) := h
    · exact Or.inl (Or.inl hp)
    · exact Or.inl (Or.inr hq)
    · exact Or.inr hr

-- __Solution__ by grind
example (p q r : Prop)
  : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
:= by grind
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
    exact Or.inl hp

-- __Solution__ by grind
example (p : Prop)
  : p ∨ False ↔ p
:= by grind
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
    exact Or.inr hp

-- __Solution__ by grind
example (p : Prop)
  : False ∨ p ↔ p
:= by grind
/-


# Conjuction and disjunction as distributive category

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
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩
  · intro h
    obtain (⟨hp, hq⟩ | ⟨hp, hr⟩) := h
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩

-- __Solution__ by grind
example (p q r : Prop)
  : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
:= by grind
