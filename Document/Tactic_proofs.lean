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
Due to the kernel being small, we were able to give a brief summary of the most important kernel-level concepts
{ref "sec-primitives"}[earlier]. In contrast, tactics implement heterogeneous automations. They cannot be summarized briefly, and learning them is more challenging than understanding the kernel-level concepts. We now illustrate two tactics, `grind` and `rw`.


# Automation with grind

The factorization of the [difference of two squares][diff-sq] can be proven by `grind`.

[diff-sq]: https://en.wikipedia.org/wiki/Difference_of_two_squares

-/
def diff_sq (x y : ℝ)
  : x^2 - y^2 = (x + y) * (x - y)
:= by
  grind
/-
When the elaborator encounters `by`, signifying a tactic block, it runs the tactic interpreter. Tactics are [imperative programs][imperative-program]. Within a tactic block they manipulate the proof state consisting of the hypotheses and the goal, and the block as a whole must produce an expression having the proposition as its type.

[imperative-program]: https://en.wikipedia.org/wiki/Imperative_programming

Above, `grind` is the only tactic in the block. It produces an expression of type `x^2 - y^2 = (x + y) * (x - y)`. The expression can be inspected using `#print`, revealing that the actual proof has the auto-generated name `diff_sq._proof_1`.
-/
#print diff_sq
#print diff_sq._proof_1
/-
The proof refers to several functions and is already long even without expanding them. Writing just `grind` amounts to significant compression. This is achieved by using algorithms inspired by modern [SMT][SMT] solvers.

[SMT]: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories


# Rewriting with rw

[Semigroup][semigroup] is a set with an associative binary operation. In Lean, semigroups are defined as a type class.{margin}[Type classes are inductive types with special elaboration-level features. We return to them {ref "sec-type-classes"}[later].]

[semigroup]: https://en.wikipedia.org/wiki/Semigroup

Here is a fact about commutative semigroups.
-/
example (G : Type) [Semigroup G] (a b c : G)
  (h : ∀ x y : G, x * y = y * x)
  : a * b * c = b * c * a
:= by
  calc
    (a * b) * c
    _ = (b * a) * c := by rw [h a b]
    _ = b * (a * c) := by grind
    _ = b * (c * a) := by rw [h a c]
    _ = (b * c) * a := by grind
/-
We use the `grind` and `rw` tactics to prove the steps in the `calc` block.{margin}[The `calc` block chains equalities, and other transitive relations.] The `rw` tactic uses the commutativity hypothesis `h` as a rewrite rule. For instance, `rw [h a b]` replaces `a * b` with `b * a`.
-/
