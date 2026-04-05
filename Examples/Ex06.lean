import Mathlib
/-

# Equivalence

Equivalence `p ↔ q` is a product type like `And`. It is implemented as a structure. Find this structure and write your own version of it.
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

Formulate and prove [biconditional elimination](https://en.wikipedia.org/wiki/Biconditional_elimination).
-/

/-


Should contain at least the following analogues of

```
α × β ≃ β × α
(α × β) × γ ≃ α × (β × γ)
α ⊕ β ≃ β ⊕ α
(α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ)
α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)
```

-/

example (p q : Prop)
  : p ∧ q ↔ q ∧ p
:= by grind

example (p q r : Prop)
  : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
:= by grind

example (p q : Prop)
  : p ∨ q ↔ q ∨ p
:= by grind

example (p q r : Prop)
  : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
:= by grind

example (p q r : Prop)
  : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
:= by grind
