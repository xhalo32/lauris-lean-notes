import Mathlib
/-

# Proofs using automation

-/
lemma diff_sq (x y : ℝ)
  : x^2 - y^2 = (x + y) * (x - y)
:= by
  grind

#print diff_sq
#print diff_sq._proof_1_1
/-

The proof uses

* properties of ℝ as a commutative ring
* classical logic

The `grind` tactic is similar to modern [SMT][SMT] solvers. It generates proofs by contradiction.

[SMT]: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories

Show [Brahmagupta's identity][brahmagupta].

[brahmagupta]: https://en.wikipedia.org/wiki/Brahmagupta%27s_identity

-/
example (n a b c d : ℝ)
  : (a^2 + n*b^2) * (c^2 + n*d^2)
    = (a*c - n*b*d)^2 + n*(a*d + b*c)^2
:= by
  -- __Solution__
  grind
/-

Show [Woodbury formula][woodbury] for scalars.

[woodbury]: https://en.wikipedia.org/wiki/Woodbury_matrix_identity

-/
example (a c u v : ℝ)
  (h1 : a + u*c*v ≠ 0) (h2 : a ≠ 0) (h3 : c ≠ 0)
  : (a + u*c*v)⁻¹ = a⁻¹ - a⁻¹*u * (c⁻¹ + v*a⁻¹*u)⁻¹ * v*a⁻¹
:= by
  -- __Solution__
  grind
/-


# Step by step proofs

Consider the following commutation.
-/
example (a b c : ℕ)
  : a * b * c = b * c * a
:= by grind
/-

In an abstract form, the commutation reads
-/
example (G : Type) [Semigroup G] (a b c : G)
  (h1 : a * b = b * a)
  (h2 : a * c = c * a)
  : a * b * c = b * c * a
:= by grind

#print Semigroup
/-

[Magma][magma] is a set with a closed binary operation. A [semigroup][semigroup] is a magma whose binary operation is associative. Magma is called `Mul` in Lean.

[magma]: https://en.wikipedia.org/wiki/Magma_(algebra)
[semigroup]: https://en.wikipedia.org/wiki/Semigroup

We define our own version of `Semigroup`.
-/
class Semigroup' (G : Type) extends Mul G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
/-

When using this version, we need to write a step by step proof (or implement further automation).
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
/-

We can replace the hypotheses `h1` and `h2` by the stronger hypothesis that the semigroup is commutative. Let us start with a single step.
-/
example (G : Type) [Semigroup' G] (a b c : G)
  (h : ∀ x y : G, x * y = y * x)
  : a * b * c = b * a * c
:= by
  rw [h a b]
/-

Show
-/
example (G : Type) [Semigroup' G] (a b c : G)
  (h : ∀ x y : G, x * y = y * x)
  : a * b * c = b * c * a
:= by
  -- __Solution__
  calc
    a * b * c
    _ = b * a * c := by rw [h a b]
    _ = b * (a * c) := by rw [Semigroup'.mul_assoc]
    _ = b * (c * a) := by rw [h a c]
    _ = b * c * a := by rw [Semigroup'.mul_assoc]
/-


# Proofs with steps and automation

Show an elementary case of [Young's inequality][young].

[young]: https://en.wikipedia.org/wiki/Young%27s_inequality_for_products#Elementary_case

-/
lemma elem_young (a b : ℝ) :
  a * b ≤ a^2/2 + b^2/2
:= by
  have : (a - b)^2 ≥ 0 := by positivity
  grind
/-


Show [Peter-Paul][peter-paul] inequality.

[peter-paul]: https://en.wikipedia.org/wiki/Young%27s_inequality_for_products#Elementary_case

-/
example (a b ε : ℝ) (h : ε > 0) :
  a * b ≤ a^2/(2*ε) + ε*b^2/2
:= calc
  a * b
  _ = (a*(√ε)⁻¹) * (√ε*b) := by
    -- __Solution__
    grind
  _ ≤ (a*(√ε)⁻¹)^2/2 + (√ε*b)^2/2 := by
    exact elem_young (a*(√ε)⁻¹) (√ε*b)
  _ = a^2/(2*ε) + ε*b^2/2 := by
    -- __Solution__
    grind
