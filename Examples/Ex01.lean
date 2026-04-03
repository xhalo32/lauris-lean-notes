import Mathlib

example (x y : ℝ)
  : x^2 - y^2 = (x + y) * (x - y)
:= by
  grind

lemma diff_sq (x y : ℝ)
  : x^2 - y^2 = (x + y) * (x - y)
:= by
  grind

#print diff_sq
#print diff_sq._proof_1_1
/-
Proof uses

* properties of ℝ as a commutative ring
* classical logic (grind uses techniques inspired by modern SMT solvers, it always attempts to derive a contradiction)

Lean consists of

* High level automation
* Low level proof checked by a relatively simple (< 9000 lines of code) program called the kernel.
-/

example (a b c : ℕ)
  : a * b * c = b * c * a
:= by
  grind

example (G : Type) [Semigroup G] (a b c : G)
  (h1 : a * b = b * a)
  (h2 : a * c = c * a)
  : a * b * c = b * c * a
:= by
  grind

#print Semigroup

/-
Magma is a set with a closed binary operation. A semigroup is a magma whose binary operation is associative. Magma is called Mul in Lean.
-/
class Semigroup' (G : Type) extends Mul G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
/-

We need to write a step by step proof (or implement further automation).

-/
example (G : Type) [Semigroup' G] (a b c : G)
  (h1 : a * b = b * a)
  (h2 : a * c = c * a)
  : a * b * c = b * c * a
:= by calc
  a * b * c
  _ = b * a * c := by rw [h1]
  _ = b * (a * c) := by rw [Semigroup'.mul_assoc]
  _ = b * (c * a) := by rw [h2]
  _ = b * c * a := by rw [Semigroup'.mul_assoc]

example (G : Type) [Semigroup' G] (a b c : G)
  (h1 : ∀ x y : G, x * y = y * x)
  : a * b * c = b * c * a
:= by
  calc
    a * b * c
    _ = b * a * c := by rw [h1 a b]
    _ = b * (a * c) := by rw [Semigroup'.mul_assoc]
    _ = b * (c * a) := by rw [h1 a c]
    _ = b * c * a := by rw [Semigroup'.mul_assoc]
