/-
Natural numbers
%%%
tag := "sec-peano"
%%%
-/
import Mathlib
/-


We will show that `ℕ` satisfies the second-order formulation of [Peano axioms][peano]:{margin}[Here `S` is the successor function.]

1. `0` is a natural number.
2. For every natural number `x`, `x = x`.
3. For all natural numbers `x` and `y`, if `x = y`, then `y = x`.
4. For all natural numbers `x`, `y` and `z`, if `x = y` and `y = z`, then `x = z`.
5. For all `a` and `b`, if `b` is a natural number and `a = b`, then `a` is also a natural number.
6. For every natural number `n`, `S n` is a natural number.
7. For all natural numbers `m` and `n`, if `S m = S n`, then `m = n`.
8. For every natural number `n`, `S n = 0` is false.
9. If `φ` is a [unary][unary] predicate such that `φ 0` is true, and for every natural number `n`, `φ n` being true implies that `φ (S n)` is true, then `φ n` is true for every natural number `n`.

[peano]: https://en.wikipedia.org/wiki/Peano_axioms
[unary]: https://en.wikipedia.org/wiki/Unary_function

We have already seen axiom 1.
-/
example : ℕ := 0
/-

Axioms 2-4 describe the equality relation.
-/
example (x : ℕ) : x = x := rfl

example (x y : ℕ) (h : x = y) : (y = x) := Eq.symm h

example (x y z : ℕ) (h1 : x = y) (h2 : y = z) : (x = z)
:= Eq.trans h1 h2
/-

We return to axiom 5 shortly. Axiom 6 is similar to axiom 1.
-/
def S := Nat.succ

example (n : ℕ) : ℕ := S n
/-

Axiom 7 states constructor injectivity.
-/
example (n m : ℕ) (h : S n = S m) : n = m := Nat.succ.inj h
/-

Axiom 8 states constructor distinctness.
-/
example (n : ℕ) : S n ≠ 0 := nofun
/-


# Axiom of induction
%%%
tag := "sec-induction"
%%%


Axiom 9 is called the [axiom of induction][axiom-of-induction].

[axiom-of-induction]: https://en.wikipedia.org/wiki/Axiom_of_induction

-/
example
  (P : ℕ → Prop)
  (h1 : P 0) (h2 : ∀ n : ℕ, P n → P (S n))
  (n : ℕ) : P n
:= Nat.rec h1 (λ m hi ↦ h2 m hi) n
/-

An explicit version reads
-/
example :
  (motive : ℕ → Sort u) /- motive -/ →

  -- minor premises:
  motive 0 /- zero -/ →
  ((m : ℕ) → motive m → motive m.succ) /- succ -/ →

  (n : ℕ) /- major premise -/ →
  motive n /- codomain -/
:= @Nat.rec

example
  (P : ℕ → Prop)
  (h1 : P 0) (h2 : ∀ n : ℕ, P n → P (S n))
  (n : ℕ) : P n
:= @Nat.rec
  (λ n ↦ P n) /- motive -/

  -- minor premises:
  h1 /- zero -/
  (λ m hi ↦ h2 m hi) /- succ -/

  n /- major premise -/
/-
What distinguishes this proof from all recursor-based proofs we have seen so far is that the induction hypothesis `hi` is essential.
-/
example (P : ℕ → Prop) (h2 : ∀ n : ℕ, P n → P (S n)) :
  let motive := λ n ↦ P n
  ((m : ℕ) → motive m → motive m.succ) :=
    (λ m hi ↦ h2 m hi)

example (P : ℕ → Prop) (h2 : ∀ n : ℕ, P n → P (S n)) :
  let motive := λ n ↦ P n
  ((m : ℕ) → motive m → motive m.succ)
    = ((n : ℕ) → P n → P (S n))
:= rfl

example (P : ℕ → Prop) :
  (∀ n : ℕ, P n → P (S n)) = ((n : ℕ) → P n → P (S n))
:= rfl
/-


# Structural recursion

Axiom 9 can be proven using pattern matching together with [structural recursion][structural-recursion].

[structural-recursion]: https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#structural-recursion

-/
lemma axiom9
  (P : ℕ → Prop)
  (h1 : P 0) (h2 : ∀ n : ℕ, P n → P (S n))
  (n : ℕ) : P n
:=
  match n with
  | 0 => h1
  | Nat.succ m => h2 m (axiom9 P h1 h2 m)
/-

Structural recursion is translated to a use an associated recursor. Here are two [primitive recursive][primitive-recursive] functions, defined with the help of structural recursion.

[primitive-recursive]: https://en.wikipedia.org/wiki/Primitive_recursive_function

-/
def add (x y : ℕ) :=
  match x with
  | 0 => y
  | Nat.succ z => Nat.succ (add z y)

def sub (y x : ℕ) :=
  let pred n :=
    match n with
    | 0 => 0
    | Nat.succ m => m
  match x with
  | 0 => y
  | Nat.succ z => pred (sub y z)
/-

They can be shown to coincide with the standard `+` and `-` on `ℕ`.
-/
example (x y : ℕ) : add x y = x + y
:= by
  induction x with
  | zero => simp [add]
  | succ z ih =>
      simp [add]
      grind

example (x y : ℕ) : sub y x = y - x
:= by
  induction x with
  | zero => simp [sub]
  | succ z ih =>
      simp [sub]
      grind
/-


# Axiom 5

Axiom 5 is awkward in Lean, since `a = b` can be formulated only when `a` and `b` have the same type. Indeed, the following example is valid
-/
example (α : Sort u) (a b : α) :
  Prop := a = b
/-
while the following is not
```lean +error
example (α : Sort u) (β : Sort v) (a : α) (b : β):
  Prop := a = b
```

Substitution can be viewed as a proxy of axiom 5.
-/
lemma proxy
  (a b : ℕ) (P : ℕ → Prop)
  (h1 : a = b) (h2 : P b) : P a
:=
  have : b = a := Eq.symm h1
  Eq.subst this h2
/-

We can use `proxy` to show, for instance, that if `b` is an even number and `a = b`, then `a` is also an even number.
-/
example
  (a b : ℕ)
  (h1 : a = b) (h2 : ∃ n : ℕ, b = 2*n)
  : ∃ n : ℕ, a = 2*n
:=
  let P (x : ℕ) := ∃ n : ℕ, x = 2*n
  proxy a b P h1 h2
/-


# Further proofs and remarks

Here is a variant of `proxy` with the two first arguments implicit.
-/
lemma proxy'
  {a b : ℕ} (P : ℕ → Prop)
  (h1 : a = b) (h2 : P b) : P a
:=
  have : b = a := Eq.symm h1
  Eq.subst this h2

example
  (a b : ℕ)
  (h1 : a = b) (h2 : ∃ n : ℕ, b = 2*n)
  : ∃ n : ℕ, a = 2*n
:=
  let P (x : ℕ) := ∃ n : ℕ, x = 2*n
  proxy' P h1 h2
/-

The following two examples boil down to constructor distinctness.
-/
example (n : ℕ) : 2*n + 1 ≠ 0 := nofun

example : ∀ n : ℕ, n^2 + 2*n + 3 ≠ 0 := nofun
/-

We claimed {ref "sec-universe-placement"}[earlier] that the following the inductive type encodes natural numbers.
-/
inductive NextLevelNat : Sort 2 where
  | zero : NextLevelNat
  | succ : NextLevelNat → NextLevelNat
/-
Let us now justify this by proving that `NextLevelNat` satisfies the second-order formulation of Peano axioms.
-/
example : NextLevelNat := NextLevelNat.zero

example (x : NextLevelNat) : x = x := rfl

example (x y : NextLevelNat) (h : x = y) : (y = x)
:= Eq.symm h

example (x y z : NextLevelNat)
  (h1 : x = y) (h2 : y = z) : (x = z)
:= Eq.trans h1 h2

example
  (a b : NextLevelNat) (P : NextLevelNat → Prop)
  (h1 : a = b) (h2 : P b) : P a
:=
  have : b = a := Eq.symm h1
  Eq.subst this h2

example (n : NextLevelNat) :
  NextLevelNat := NextLevelNat.succ n

example (n m : NextLevelNat)
  (h : n.succ = m.succ) : n = m := NextLevelNat.succ.inj h

example (n : NextLevelNat) :
  n.succ ≠ NextLevelNat.zero := nofun

example
  (P : NextLevelNat → Prop)
  (h1 : P NextLevelNat.zero)
  (h2 : ∀ n : NextLevelNat, P n → P (n.succ))
  (n : NextLevelNat) : P n
:= NextLevelNat.rec h1 (λ m hi ↦ h2 m hi) n
