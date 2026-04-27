import Mathlib
/-

# Ordering

Similarly to the class hierarchy that is related to addition and starts from `Add`, there is a hierarchy related to orderings. The base class playing the role of `Add` is `LE`.

We define a type of four elements, giving names to four finite sets of natural numbers, and define an ordering based on subset inclusion of the associated sets.
-/
inductive X
  | a
  | b
  | c
  | d

def X.toSet : X → Finset ℕ
| a => {1}
| b => {2}
| c => {1,2,3}
| d => {1,2,4}

open X in
instance : LE X where
  le x y := toSet x ⊆ toSet y

open X in
example : a ≤ c := by
  simp [LE.le]
  decide
/-

Show that `≤` on `X` is a [preorder][preorder].

[preorder]: https://en.wikipedia.org/wiki/Preorder

-/
instance : Preorder X where
  le_refl := by
    -- __Solution__
    intro x
    simp [LE.le]
  le_trans := by
    intro x y z
    -- __Solution__
    simp [LE.le]
    grind
/-

Show that `≤` on `X` is a [partial order][partial-order].

[partial-order]: https://en.wikipedia.org/wiki/Partially_ordered_set

-/
open X in
instance : PartialOrder X where
  le_antisymm := by
    -- __Solution__
    intro x y hx hy
    cases x <;> cases y <;> simp [LE.le, toSet] at * <;>
    contradiction
/-

Show that `a` and `b` don't have a [least upper bound][least-ub], implying that `X` is not a [lattice][lattice].

[least-ub]: https://en.wikipedia.org/wiki/Join_and_meet#Partial_order_approach
[lattice]: https://en.wikipedia.org/wiki/Lattice_(order)

-/
open X in
example
  : ¬∃ L, a ≤ L ∧ b ≤ L ∧ ∀ L', a ≤ L' ∧ b ≤ L' → L ≤ L'
:= by
  -- __Solution__
  simp
  intro L ha hb
  cases L <;> simp [LE.le, toSet] at * <;>
  solve
  | use d
    decide
  | use c
    decide
