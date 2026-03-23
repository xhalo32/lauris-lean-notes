/-
Quotient types
%%%
tag := "sec-quotient-types"
%%%
-/
import Mathlib
import Document.Type_classes
/-
```lean -show
open Document.Peano
open Document.Type_classes
```
Integers can be encoded as the quotient set of $`\mathbb N^2` by the equivalence relation $`\sim`, where $`(n_1, k_1) \sim (n_2, k_2)` if and only if $`n_1 + k_2 = n_2 + k_1`.{margin}[Using integers, the relation can be rewritten as $`n_1 - k_1 = n_2 - k_2`.] Positive integers are then given by the [equivalence classes][equivalence-class] $`[(n, 0)]`, $`n \in \mathbb N`, and negative integers by $`[(0, k)]`, $`k \in \mathbb N`. We will use this encoding to implement integers based on `Nat'`.{margin}[We have imported our earlier definitions.]

[equivalence-class]: https://en.wikipedia.org/wiki/Equivalence_class

The equivalence relation is encoded by
-/
def r (p₁ p₂ : Nat' × Nat') : Prop :=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  n₁.add k₂ = n₂.add k₁
/-

It inherits reflexivity and symmetry from equality.
-/
lemma r_refl (p : Nat' × Nat') : r p p := rfl

lemma r_symm {p₁ p₂ : Nat' × Nat'}
  (h : r p₁ p₂)
  : r p₂ p₁
:= h.symm
/-

Transtivity is shown using properties of addition on `Nat'`.
-/
lemma r_trans {p₁ p₂ p₃ : Nat' × Nat'}
  (h1 : r p₁ p₂) (h2 : r p₂ p₃)
  : r p₁ p₃
:= by
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  let ⟨n₃, k₃⟩ := p₃
  simp only [r] at *
  have (x y z : Nat') := calc
    (x.add y).add z
    _ = x.add (y.add z) := by simp only [Nat'.add_assoc]
    _ = x.add (z.add y) := by simp only [Nat'.add_comm]
    _ = (x.add z).add y := by simp only [Nat'.add_assoc]
  have := calc
    (n₁.add k₃).add k₂
    _ = (n₁.add k₂).add k₃ := by simp only [this]
    _ = (n₂.add k₁).add k₃ := by simp only [h1]
    _ = (n₂.add k₃).add k₁ := by simp only [this]
    _ = (n₃.add k₂).add k₁ := by simp only [h2]
    _ = (n₃.add k₁).add k₂ := by simp only [this]
  exact Nat'.add_right_cancel this
/-

A [setoid][setoid] is a set equipped with an equivalence relation.

[setoid]: https://en.wikipedia.org/wiki/Setoid

-/
instance s : Setoid (Nat' × Nat') where
  r := r
  iseqv := ⟨r_refl, r_symm, r_trans⟩
/-

A quotient type is formed from a setoid. The formation of quotient types is a primitive feature implemented in the kernel. It is analogous to, but distinct from, the formation of inductive types.
-/
def Int' : Type := Quotient s
