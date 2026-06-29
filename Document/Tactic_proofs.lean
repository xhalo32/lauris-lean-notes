/-
Tactic proofs
%%%
tag := "sec-tactic-proofs"
%%%
-/
import Mathlib
/-
-/
-- -show
namespace Document.Tactic_proofs
/-
Due to the kernel being small, we were able to give a brief {ref "sec-primitives"}[summary] of the most important kernel-level concepts. In contrast, tactics implement heterogeneous automation. They cannot be summarized briefly, and learning them is more challenging than understanding the kernel-level concepts. We now illustrate two tactics, [grind][grind] and [simp][simp].

[grind]: https://lean-lang.org/doc/reference/latest/The--grind--tactic/#grind-tactic
[simp]: https://lean-lang.org/doc/reference/latest/The-Simplifier/#the-simplifier

# Automation with grind

The factorization of the [difference of two squares][diff-sq] can be proven by `grind`.

[diff-sq]: https://en.wikipedia.org/wiki/Difference_of_two_squares

-/
example (x y : ℝ)
  : x^2 - y^2 = (x + y) * (x - y)
:= by
  grind
/-
When the elaborator encounters `by`, signifying a tactic block, it runs the tactic interpreter. Tactics are [imperative programs][imperative-program]. Within a tactic block they manipulate the proof state consisting of the hypotheses and the goal, and the block as a whole must produce an expression having the proposition as its type.

[imperative-program]: https://en.wikipedia.org/wiki/Imperative_programming

Above, `grind` is the only tactic in the block. It produces an expression of type `x^2 - y^2 = (x + y) * (x - y)`.

We can give a name to a proven proposition in several ways, and use it in subsequent proofs. {index}[lemma] {index}[theorem]
-/
def diff_sq₁ (x y : ℝ) : x^2 - y^2 = (x + y) * (x - y)
:= by grind

lemma diff_sq₂ (x y : ℝ) : x^2 - y^2 = (x + y) * (x - y)
:= by grind

theorem diff_sq₃ (x y : ℝ) : x^2 - y^2 = (x + y) * (x - y)
:= diff_sq₁ x y
/-
Despite the syntactic differences, all these define the same function.

The expression produced by `grind` can be inspected using `#print`. The actual proof has an auto-generated name.
-/
#print diff_sq₂
#print diff_sq₁._proof_1
/-
The proof refers to several functions and is already long even without expanding them. Writing just `grind` amounts to significant compression. This is achieved by using algorithms inspired by modern [SMT][SMT] solvers.

[SMT]: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories


# Rewriting with simp

[Semigroup][semigroup] is a set with an associative binary operation. In Lean, semigroups are defined as a type class.{margin}[Type classes are inductive types with special elaboration-level features. We return to them {ref "sec-type-classes"}[later].]

[semigroup]: https://en.wikipedia.org/wiki/Semigroup

Here is a fact about a semigroup together with a commutativity hypothesis.
-/
example (G : Type) [Semigroup G] (a b c : G)
  (h : ∀ x y : G, x * y = y * x)
  : a * b * c = b * c * a
:= by
  calc
    (a * b) * c
    _ = (b * a) * c := by simp [h]
    _ = b * (a * c) := by grind
    _ = b * (c * a) := by simp [h]
    _ = (b * c) * a := by grind
/-
We use the `grind` and `simp` tactics to prove the steps in the `calc` block.{margin}[The `calc` block chains equalities and other transitive relations.] The `simp` tactic uses the commutativity hypothesis `h` as a rewrite rule.


# Further proofs

-/
example : diff_sq₁ = diff_sq₂ := rfl
example : diff_sq₁ = diff_sq₃ := rfl
