/-
Quotient types
%%%
tag := "sec-quotient-types"
%%%
-/
import Mathlib.Data.Quot
import Document.Type_classes
/-
Integers can be encoded as the quotient set of $`\mathbb N^2` by the equivalence relation $`\sim`, where $`(n_1, k_1) \sim (n_2, k_2)` if and only if $`n_1 + k_2 = n_2 + k_1`.{margin}[Using integers, the relation can be rewritten as $`n_1 - k_1 = n_2 - k_2`.] Positive integers are then given by the [equivalence classes][equivalence-class] $`[(n, 0)]`, $`n \in \mathbb N`, and negative integers by $`[(0, k)]`, $`k \in \mathbb N`. We will use this encoding to implement integers based on `Nat'`.{margin}[We have imported our earlier definitions.]

[equivalence-class]: https://en.wikipedia.org/wiki/Equivalence_class

The equivalence relation is encoded by
-/
def N2.r (p₁ p₂ : Nat' × Nat') : Prop :=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  n₁ + k₂ = n₂ + k₁
/-

It inherits reflexivity and symmetry from equality.
-/
lemma N2.r_refl (p : Nat' × Nat') : r p p := rfl

lemma N2.r_symm {p₁ p₂ : Nat' × Nat'}
  (h : r p₁ p₂)
  : r p₂ p₁
:= h.symm
/-

Transtivity is shown using properties of addition on `Nat'`. We isolate a step in the proof as a lemma that will be reused.
-/
lemma Nat'.add_right_comm {a b c : Nat'}
  : a + b + c = a + c + b
:=
  calc
    (a + b) + c
    _ = a + (b + c) := add_assoc
    _ = a + (c + b) := congrArg (a + ·) add_comm
    _ = (a + c) + b := add_assoc.symm

open Nat' in
lemma N2.r_trans {p₁ p₂ p₃ : Nat' × Nat'}
  (h1 : r p₁ p₂) (h2 : r p₂ p₃)
  : r p₁ p₃
:=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  let ⟨n₃, k₃⟩ := p₃
  have := calc
    (n₁ + k₃) + k₂
    _ = (n₁ + k₂) + k₃ := add_right_comm
    _ = (n₂ + k₁) + k₃ := congrArg (· + k₃) h1
    _ = (n₂ + k₃) + k₁ := add_right_comm
    _ = (n₃ + k₂) + k₁ := congrArg (· + k₁) h2
    _ = (n₃ + k₁) + k₂ := add_right_comm
  add_right_cancel this
/-


# Formation of quotient types

A quotient type is formed from a [setoid][setoid], a set equipped with an equivalence relation.

[setoid]: https://en.wikipedia.org/wiki/Setoid

-/
#print Setoid

instance N2.instSetoid : Setoid (Nat' × Nat') where
  r := r
  iseqv := ⟨r_refl, r_symm, r_trans⟩
/-

The formation of a quotient type is a primitive feature implemented in the kernel. It is analogous to, but distinct from, the formation of inductive types.
-/
def Z : Type := Quotient N2.instSetoid
/-

Expressions of type `Z` can be introduced using `Quotient.mk`, coming with syntactic sugar.
-/
open Nat' in
example
  : Quotient.mk N2.instSetoid (zero, zero) = ⟦(zero, zero)⟧
:= rfl

def Z.zero : Z := ⟦(Nat'.zero, Nat'.zero)⟧
/-

The equivalence relation bundled in `Setoid` comes with syntactic sugar.
-/
example (p q : Nat' × Nat') : (p ≈ q) = N2.r p q := rfl
/-


# Elimination of quotient expressions

Functions from quotients can be defined by proving that a function from the underlying type respects the quotient's equivalence relation.
-/
def N2.add (p₁ p₂ : Nat' × Nat') :=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  (n₁ + n₂, k₁ + k₂)

open Nat' in
lemma N2.add_resp_r {p₁ q₁ p₂ q₂ : Nat' × Nat'}
  (h1 : p₁ ≈ q₁) (h2 : p₂ ≈ q₂)
  : add p₁ p₂ ≈ add q₁ q₂
:=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  let ⟨m₁, l₁⟩ := q₁
  let ⟨m₂, l₂⟩ := q₂
  have {a b c d : Nat'} := calc
    (a + b) + (c + d)
    _ = ((a + b) + c) + d := add_assoc.symm
    _ = ((a + c) + b) + d := congrArg (· + d) add_right_comm
    _ = (a + c) + (b + d) := add_assoc
  calc
    (n₁ + n₂) + (l₁ + l₂)
    _ = (n₁ + l₁) + (n₂ + l₂) := this
    _ = (m₁ + k₁) + (n₂ + l₂) := congrArg (· + (n₂ + l₂)) h1
    _ = (m₁ + k₁) + (m₂ + k₂) := congrArg ((m₁ + k₁) + ·) h2
    _ = (m₁ + m₂) + (k₁ + k₂) := this.symm

def Z.add := Quotient.lift₂
  (λ p q ↦ Quotient.mk N2.instSetoid (N2.add p q))
  (λ _ _ _ _ h1 h2 ↦ Quotient.sound (N2.add_resp_r h1 h2))
/-

Here `Quotient.sound` is the quotient axiom.
-/
example (α : Sort u) (s : Setoid α) (a b : α) :
  a ≈ b → (Quotient.mk s a) = (Quotient.mk s b)
:= Quotient.sound
/-

We can now show that `1 - 1 = 0`.
-/
instance : Add' Z where
  add := Z.add

def Z.one : Z := ⟦(Nat'.zero.succ, Nat'.zero)⟧
def Z.minus_one : Z := ⟦(Nat'.zero, Nat'.zero.succ)⟧

open Z in
example : one + minus_one = zero := Quotient.sound rfl
/-

The standard integers are not defined as a quotient, and computing with them does not require using the quotient axiom.
-/
