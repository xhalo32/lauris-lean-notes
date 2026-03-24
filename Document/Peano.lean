/-
Natural numbers
%%%
tag := "sec-peano"
%%%
-/
import Mathlib.Computability.Ackermann
/-
-/
-- -show
namespace Document.Peano
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
9. If `φ` is a predicate such that `φ 0` is true, and for every natural number `n`, `φ n` being true implies that `φ (S n)` is true, then `φ n` is true for every natural number `n`.

[peano]: https://en.wikipedia.org/wiki/Peano_axioms

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


# Recursion

Axiom of induction can be proven using pattern matching together with [structural recursion][structural-recursion].

[structural-recursion]: https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#structural-recursion

-/
lemma axiom9
  (P : ℕ → Prop)
  (h1 : P 0) (h2 : ∀ n : ℕ, P n → P (S n))
  (n : ℕ) : P n
:=
  match n with
  | 0 => h1
  | Nat.succ n => h2 n (axiom9 P h1 h2 n)
/-

Structural recursions are translated to evaluations of recursors. As an illustration, we consider a [primitive recursive][primitive-recursive] function, defined in two ways.

[primitive-recursive]: https://en.wikipedia.org/wiki/Primitive_recursive_function

-/
def add (x y : ℕ) :=
  match y with
  | Nat.zero => x
  | Nat.succ y => Nat.succ (add x y)

def add₁ (x y : ℕ) : ℕ := Nat.rec x (λ _ hi ↦ Nat.succ hi) y
/-

Both versions coincide with `+` on `ℕ`.
-/
lemma add_coincides (x y : Nat) : add x y = x + y
:=
  match y with
  | 0 => rfl
  | y + 1 => congrArg Nat.succ (add_coincides x y)

example (x y : Nat) : add₁ x y = x + y
:= Nat.rec rfl (λ _ hi ↦ congrArg Nat.succ hi) y
/-


## Ackermann function

The expressive power of `Nat.rec` extends well beyond primitive recursive functions. The [Ackermann function][ackermann] is a [computable function][computable-function] that is not primitive recursive.

[ackermann]: https://en.wikipedia.org/wiki/Ackermann_function
[computable-function]: https://en.wikipedia.org/wiki/Computable_function

-/
def ackermann : Nat → Nat → Nat := Nat.rec
  (λ n ↦ n + 1)
  (λ _ hi1 ↦ Nat.rec
    (hi1 1)
    (λ _ hi2 ↦ hi1 hi2)
  )
/-

It can be defined in a natural way using pattern matching.
-/
def ackermann' (m n : ℕ) :=
  match m, n with
  | 0, n => n + 1
  | m + 1, 0 => ackermann' m 1
  | m + 1, n + 1 => ackermann' m (ackermann' (m + 1) n)
/-
However, this version is not translated to a nested use of `Nat.rec` as above. Instead, it uses [well-founded recursion][well-founded-recursion]. Mathlib's {lean}`ack` is defined in the same way as `ackermann'`. Both our versions coincide with {lean}`ack`.

[well-founded-recursion]: https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#well-founded-recursion

-/
example : ack = ackermann := by
  funext m
  simp only [ackermann]
  induction m with
  | zero =>
      funext _
      simp
  | succ _ ih =>
      funext n
      induction n with
      | zero =>
          simp [ih]
      | succ _ ihn =>
          simp [ih, ihn]
/-


# Proofs by induction

We define addition on our version of natural numbers and prove some properties that will be used later when we define our version of integers.

-/
-- -show
-- Expose names for later import
end Document.Peano
/-
-/
inductive Nat' : Type where
  | zero : Nat'
  | succ : Nat' → Nat'

def Nat'.add (x y : Nat') :=
  match y with
  | zero => x
  | succ y => succ (add x y)
/-
Here `add` is defined in the namespace `Nat'`, and names from `Nat'` are available unqualified in the definition.

Zero is a [left identity element][identity-element] of addition.{margin}[It is also a right identity element. This can be proven by `rfl`, as seen in the below proof of right cancellation.] The proof uses the congruence property of equality.

[identity-element]: https://en.wikipedia.org/wiki/Identity_element

-/
lemma Nat'.zero_add (n : Nat')
  : zero.add n = n
:=
  match n with
  | zero => rfl
  | succ n => congrArg succ n.zero_add
/-

The successor function is [equivariant][equivariant] under addition.

[equivariant]: https://en.wikipedia.org/wiki/Equivariant_map

-/
lemma Nat'.add_succ (n m : Nat')
  : n.add m.succ = (n.add m).succ
:=
  match m with
  | zero => rfl
  | succ m => congrArg succ (n.add_succ m)

lemma Nat'.succ_add (n m : Nat')
  : n.succ.add m = (n.add m).succ
:=
  match m with
  | zero => rfl
  | succ m => congrArg succ (n.succ_add m)
/-
Both these equivariance proofs are analogous to the proof left identity, and so is the following proof of [associativity][associativity] of addition.

[associativity]: https://en.wikipedia.org/wiki/Associative_property

-/
lemma Nat'.add_assoc (a b c : Nat')
  : (a.add b).add c = a.add (b.add c)
:=
  match c with
  | zero => rfl
  | succ c => congrArg succ (a.add_assoc b c)
/-

Addition has the [right cancellation property][right-cancellation-property].{margin}[We leave the corresponding left cancellation property as an exercise.] The proof uses the constructor injectivity.

[right-cancellation-property]: https://en.wikipedia.org/wiki/Cancellation_property
-/
lemma Nat'.add_right_cancel {n m k : Nat'}
  (h : m.add n = k.add n)
  : m = k
:=
  match n with
  | zero => calc
    m = m.add zero := rfl
    _ = k.add zero := h
    _ = k := rfl
  | succ _ => add_right_cancel (succ.inj h)
/-

Addition is [commutative][commutative]. The proof uses the symmetry of equality.

[commutative]: https://en.wikipedia.org/wiki/Commutative_property

-/
lemma Nat'.add_comm {n m : Nat'}
  : n.add m = m.add n
:=
  match m with
  | zero => calc
    n.add zero
    _ = n := rfl
    _ = zero.add n := (zero_add n).symm
  | succ m => calc
    n.add m.succ
    _ = (n.add m).succ := add_succ n m
    _ = (m.add n).succ := congrArg succ add_comm
    _ = m.succ.add n := (succ_add m n).symm
/-


# Recursive relations

Inequality `≤` on `Nat` is defined as an inductive type.
-/
#print Nat.le
/-
It has two constructors `Nat.le.refl` and `Nat.le.step`. The former is analogous to `Eq.refl`, while the latter encodes the implication: if `n ≤ m` then `n ≤ m + 1`.

We define our version and prove some properties.
-/
inductive Nat'.le (n : Nat') : Nat' → Prop
  | refl : n.le n
  | step {m : Nat'} : n.le m → n.le m.succ
/-

The smallest natural number is `zero`.
-/
lemma Nat'.zero_smallest (n : Nat')
  : zero.le n
:=
  match n with
  | zero => le.refl
  | succ n => le.step (zero_smallest n)
/-

The successor function preserves inequality.
-/
lemma Nat'.le_succ {n m : Nat'}
  (h : n.le m)
  : (n.succ.le m.succ)
:=
  match h with
  | le.refl => le.refl
  | le.step h => le.step (le_succ h)
/-

Inequality is transitive.
-/
lemma Nat'.le_trans {n m k : Nat'}
  (h1 : n.le m) (h2 : m.le k)
  : n.le k
:=
  match h2 with
  | le.refl => h1
  | le.step h2 => le.step (le_trans h1 h2)
/-
-/
-- -show
namespace Document.Peano
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

Our two versions of the Ackermann function coincide.
-/
example : ackermann' = ackermann := by
  funext m
  simp only [ackermann]
  induction m with
  | zero =>
      funext n
      simp [ackermann']
  | succ m ih =>
      funext n
      induction n with
      | zero =>
          simp [ackermann', ih]
      | succ n ihn =>
          simp [ackermann', ih, ihn]
/-

Here is a variant of `proxy` with the first two arguments implicit.
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
