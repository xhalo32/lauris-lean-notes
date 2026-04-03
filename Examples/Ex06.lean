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
