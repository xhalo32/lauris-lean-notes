/-
Axioms on equality
%%%
tag := "sec-axioms-eq"
%%%
-/
import Mathlib
/-

The quotient axiom and propositional extensionality postulate equality assuming equivalence. They differ in the nature of the equivalence.

The quotient axiom asserts that `⟦x⟧ = ⟦y⟧` if `x ≈ y`.
-/
#print Quot.sound

example (α : Sort u) (r : α → α → Prop) (x y : α)
  (h : r x y)
  : Quot.mk r x = Quot.mk r y
:= Quot.sound h
/-
We will show below that the quotient axiom implies function extensionality.

The axiom of propositional extensionality asserts that `p = q` if `p ↔ q`.
-/
#print propext

example (p q : Prop)
  (h : p ↔ q)
  : p = q
:= propext h
/-
We will show below that propositional extensionality implies quotient exactness.

Here is a small example illustrating that Lean tracks the axioms that each proof depends on.
-/
lemma t_eq_notf : True = ¬False
:= propext ⟨λ h ↦ id, λ h ↦ trivial⟩

#print axioms t_eq_notf
/-


# Function extensionality
%%%
tag := "sec-function-extensionality-proof"
%%%

Recall that function extensionality is formulated as follows.
-/
#print funext
#print axioms funext

example (α : Sort u) (β : α → Sort v) (f g : (x : α) → β x)
  (h : ∀ x, f x = g x)
  : f = g
:= funext h
/-
The proof of `funext` is based on defining an equivalence of functions by `∀ x, f x = g x`, lifting function application on the equivalence classes, and using the quotient axiom together with the {ref "sec-quotient-reduction"}[quotient reduction].
-/
example (α : Sort u) (β : α → Sort v) (f g : (x : α) → β x)
  (h : ∀ x, f x = g x)
  : f = g
:=
  -- Definition of a setoid of functions
  let Φ := (x : α) → β x
  let r (φ₁ φ₂ : Φ) := ∀ x, φ₁ x = φ₂ x
  have r_refl (φ : Φ) : r φ φ
    := λ x ↦ rfl
  have r_symm {φ₁ φ₂ : Φ} (h : r φ₁ φ₂) : r φ₂ φ₁
    := λ x ↦ (h x).symm
  have r_trans {φ₁ φ₂ φ₃ : Φ} (h1 : r φ₁ φ₂) (h2 : r φ₂ φ₃)
    : r φ₁ φ₃
    := λ x ↦ calc
      φ₁ x
      _ = φ₂ x := h1 x
      _ = φ₃ x := h2 x
  let s : Setoid Φ := ⟨r, ⟨r_refl, r_symm, r_trans⟩⟩
  -- Lift of function application
  let lifted_app (φ : Quotient s) (x : α) :=
    have {φ₁ φ₂ : Φ} (h : φ₁ ≈ φ₂) : φ₁ x = φ₂ x := h x
    Quotient.lift (λ ψ ↦ ψ x) (λ _ _ h ↦ this h) φ
  -- Use the quotient axiom
  have : ⟦f⟧ = ⟦g⟧ := Quotient.sound h
  -- Use the quotient reduction
  calc
    f = lifted_app ⟦f⟧ := rfl
    _ = lifted_app ⟦g⟧ := congrArg lifted_app this
    _ = g := rfl
/-


# Quotient exactness
%%%
tag := "sec-quotient-exactness-proof"
%%%

Recall that `Quotient.exact` is the implication converse to `Quotient.sound`.
-/
#print Quotient.exact
#print axioms Quotient.exact

example (α : Sort u) (s : Setoid α) (a₁ a₂ : α)
  (h : (⟦a₁⟧ : Quotient s) = ⟦a₂⟧)
  : a₁ ≈ a₂
:= Quotient.exact h
/-
The proof of `Quotient.exact` is based on turning the logical equivalence in the below lemma `eqv_iff` into equality using `propext`. In order to use `≈` in `calc` blocks, we declare a local instance of `Trans`.
-/
open Setoid in
lemma eqv_iff {α : Sort u} {s : Setoid α} {x₁ y₁ x₂ y₂ : α}
  (hx : x₁ ≈ x₂) (hy: y₁ ≈ y₂)
  : (x₁ ≈ y₁) ↔ (x₂ ≈ y₂)
:=
  let : Trans (α := α) (· ≈ ·) (· ≈ ·) (· ≈ ·) := ⟨trans⟩
  have mp := λ h ↦ calc
    x₂
    _ ≈ x₁ := symm hx
    _ ≈ y₁ := h
    _ ≈ y₂ := hy
  have mpr := λ h ↦ calc
    x₁
    _ ≈ x₂ := hx
    _ ≈ y₂ := h
    _ ≈ y₁ := symm hy
  ⟨mp, mpr⟩
/-

We now prove `Quotient.exact` by lifting `≈` and using the recursor of `=`.
-/
example (α : Sort u) (s : Setoid α) (a₁ a₂ : α)
  (h : (⟦a₁⟧ : Quotient s) = ⟦a₂⟧)
  : a₁ ≈ a₂
:=
  let lifted_eqv (q₁ q₂ : Quotient s) : Prop :=
    Quotient.lift₂
      (λ x y ↦ x ≈ y)
      (λ _ _ _ _ hx hy ↦ propext (eqv_iff hx hy))
      q₁ q₂
  let q₁ := ⟦a₁⟧
  have : lifted_eqv q₁ q₁ :=
    Quotient.ind (motive := λ q ↦ lifted_eqv q q) s.refl q₁
  Eq.rec (motive := λ q _ ↦ lifted_eqv q₁ q) this h
