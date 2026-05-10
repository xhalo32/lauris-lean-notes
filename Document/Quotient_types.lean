/-
Quotient types
%%%
tag := "sec-quotient-types"
%%%
-/
import Mathlib.Data.Quot
import Document.Type_classes
/-

Quotient types encode [equivalence classes][equivalence-class]. As an example, we consider integers as the quotient set of $`\mathbb N^2` by the equivalence relation $`\sim`, where $`(n_1, k_1) \sim (n_2, k_2)` if and only if $`n_1 + k_2 = n_2 + k_1`.{margin}[Using integers, the relation can be rewritten as $`n_1 - k_1 = n_2 - k_2`.] Positive integers are then given by the equivalence classes $`[(n, 0)]`, $`n \in \mathbb N \setminus \{0\}`, and negative integers by $`[(0, k)]`, $`k \in \mathbb N \setminus \{0\}`.

[equivalence-class]: https://en.wikipedia.org/wiki/Equivalence_class

We will implement integers as the quotient type by the relation{margin}[We have imported our earlier definitions.]
-/
def N2.r (p₁ p₂ : Nat' × Nat') : Prop :=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  n₁ + k₂ = n₂ + k₁
/-
We begin by showing that `r` is an equivalence relation.


# Equivalence relations

An [equivalence relation][equivalence-relation] is a binary relation that is reflexive, symmetric, and transitive. We show that `r` has these three properties. Reflexivity and symmetry are inherited from equality.

[equivalence-relation]: https://en.wikipedia.org/wiki/Equivalence_relation

-/
lemma N2.r_refl (p : Nat' × Nat') : r p p := rfl

lemma N2.r_symm {p q : Nat' × Nat'}
  (h : r p q)
  : r q p
:= h.symm
/-

Transitivity follows from properties of addition on `Nat'`. We isolate a step in the proof as a lemma that will be reused.
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

A quotient type is formed from a [setoid][setoid], a set equipped with an equivalence relation, encoded as the type class `Setoid`.

[setoid]: https://en.wikipedia.org/wiki/Setoid

-/
#print Setoid

instance N2.instSetoid : Setoid (Nat' × Nat') where
  r := r
  iseqv := ⟨r_refl, r_symm, r_trans⟩
/-

The equivalence relation bundled in `Setoid` comes with syntactic sugar.
-/
example (p q : Nat' × Nat') : (p ≈ q) = N2.r p q := rfl
/-

Like formation of inductive types using `inductive`, the formation of a quotient type is a primitive feature implemented in the kernel. The primitive is called `Quot`. Like a recursor, it has a function type but is built into the kernel.
-/
example (α : Sort u) : (α → α → Prop) → Sort u := Quot
/-
`Quot` takes a relation as its argument. The variant `Quotient`, parameterized by a setoid, is preferred in practice. It lets instance synthesis find the relation rather than requiring it to be passed explicitly.
-/
example (α : Sort u) : Setoid α → Sort u := Quotient

example (α : Sort u) (s : Setoid α) :
  Quotient s = Quot s.r
:= rfl
/-

Integers are encoded by
-/
def Z : Type := Quotient N2.instSetoid
/-


# Introduction of quotient expressions

Expressions of a quotient type are introduced using `Quot.mk`. Like `Quot`, it has a function type but is built into the kernel.
-/
example (α : Sort u) :
  (r : α → α → Prop) → α → Quot r := Quot.mk
/-
The variant `Quotient.mk` is parameterized by a setoid.
-/
example (α : Sort u) :
  (s : Setoid α) → α → Quotient s := Quotient.mk

example (α : Sort u) (s : Setoid α) :
  Quotient.mk s = Quot.mk s.r
:= rfl
/-

The following syntactic sugar is provided.
-/
example (α : Sort u) (s : Setoid α) (a : α) :
  Quotient.mk s a = ⟦a⟧
:= rfl
/-

We introduce `0` as an integer.
-/
def Z.zero : Z := ⟦(Nat'.zero, Nat'.zero)⟧
/-


# Equality of quotient expressions

Beyond formation, introduction, and elimination, quotients are characterized by an axiom relating equality of classes to the underlying equivalence.


## Quotient axiom

Axioms are propositions postulated without proof. `Quot.sound` is one of the small number of axioms postulated by the kernel.{margin}[`Quotient.sound` is essentially synonymous with `Quot.sound`. We prefer the latter to emphasize its role as an axiom.]
-/
#print Quot.sound

example (α : Sort u) (r : α → α → Prop) (a b : α)
  (h : r a b)
  : Quot.mk r a = Quot.mk r b
:= Quot.sound h

example (α : Sort u) (s : Setoid α) (a b : α)
  (h : a ≈ b)
  : Quotient.mk s a = Quotient.mk s b
:= Quot.sound h
/-

An integer `⟦(n, k)⟧` is zero if and only if `n = k`. We show now the _if_ direction. The _only if_ direction is shown later.
-/
open Nat' in
example (n k : Nat')
  (h : n = k)
  : ⟦(n, k)⟧ = Z.zero
:=
  have : (n, k) ≈ (zero, zero) := calc
    n + zero
    _ = zero + n := add_comm
    _ = n := zero_add
    _ = k := h
    _ = zero + k := zero_add.symm
  Quot.sound this
/-


## Quotient exactness

The implication opposite to `Quot.sound` is called `Quotient.exact`. Contrary to `Quot.sound`, it is a regular theorem, not an axiom.
-/
example  (α : Sort u) (s : Setoid α) (a b : α)
  (h : (⟦a⟧ : Quotient s) = ⟦b⟧)
  : a ≈ b
:= Quotient.exact h
/-

We are now ready to prove the _only if_ direction of the characterization of zero.
-/
open Nat' in
example (n k : Nat')
  (h : ⟦(n, k)⟧ = Z.zero)
  : n = k
:=
  have : (n, k) ≈ (zero, zero) := Quotient.exact h
  calc
    n = zero + n := zero_add.symm
    _ = n + zero := add_comm
    _ = zero + k := this
    _ = k := zero_add
/-

The non-negative integers give an embedding of natural numbers.
-/
open Nat' in
example (n m : Nat')
  (h : (⟦(n, zero)⟧ : Z) = ⟦(m, zero)⟧)
  : n = m
:=
  have : (n, zero) ≈ (m, zero) := Quotient.exact h
  calc
    n = zero + n := zero_add.symm
    _ = n + zero := add_comm
    _ = m + zero := this
    _ = zero + m := add_comm
    _ = m := zero_add
/-


# Elimination of quotient expressions

Functions from quotients can be defined by proving that a function from the underlying type respects the quotient's equivalence relation. This elimination principle is `Quot.lift`. Like the introduction principle `Quot.mk`, it has a function type but is built into the kernel.
-/
example (α : Sort u) (r : α → α → Prop) (β : Sort v)
  (f : α → β)
  (h : ∀ (x y : α), r x y → f x = f y) :
  Quot r → β := Quot.lift f h
/-
The variant `Quotient.lift` is parametrized by a setoid.
-/
example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → β)
  (h : ∀ (x y : α), x ≈ y → f x = f y) :
  Quotient s → β := Quotient.lift f h

example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → β)
  (h : ∀ (x y : α), x ≈ y → f x = f y)
  : Quotient.lift f h = Quot.lift f h
:= rfl
/-

In order to define negation on `Z`, we first define negation on `Nat' × Nat'` and show that it respects `N2.r`.
-/
def N2.neg (p : Nat' × Nat') :=
  let ⟨n, k⟩ := p
  (k, n)

open Nat' in
lemma N2.neg_resp_r {p q : Nat' × Nat'}
  (h : p ≈ q)
  : neg p ≈ neg q
:=
  let ⟨n, k⟩ := p
  let ⟨m, l⟩ := q
  calc
    k + m
    _ = m + k := add_comm
    _ = n + l := h.symm
    _ = l + n := add_comm
/-

The codomain of the lifted negation should be `Z`. For this reason, we need to turn `N2.neg` into a function from `Nat' × Nat'` to `Z` having the below property `h`.
-/
example (f : Nat' × Nat' → Z)
  (h : ∀ (x y : Nat' × Nat'), x ≈ y → f x = f y) :
  Z → Z := Quotient.lift f h
/-
A suitable function is obtained via introduction.
-/
example : Nat' × Nat' → Z := λ p ↦ ⟦N2.neg p⟧
/-
The required property follows from `N2.neg_resp_r` and `Quot.sound`. We define negation on `Z` by
-/
def Z.neg := Quotient.lift
  (λ p ↦ ⟦N2.neg p⟧)
  (λ _ _ h ↦ Quot.sound (N2.neg_resp_r h))
/-


# Quotient reduction

Analogously to {ref "sec-iota-reduction"}[$`\iota`-reduction] that governs the composition of elimination and introduction of expressions of an inductive type, quotient reduction causes `Quotient.lift` to reduce when composed with `Quotient.mk`.
-/
example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → β) (x : α)
  (h : ∀ (x y : α), x ≈ y → f x = f y)
  : Quotient.lift f h (Quotient.mk s x) = f x
:= rfl

variable (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → β) (x : α)
  (h : ∀ (x y : α), x ≈ y → f x = f y)
in
#reduce Quotient.lift f h (Quotient.mk s x)
/-

Quotient reduction enables the following.
-/
open Z in
example : neg zero = zero := rfl

example (n k : Nat') :
  Z.neg ⟦(n, k)⟧ = ⟦(k, n)⟧
:= rfl

example (n k : Nat') :
  Z.neg (Z.neg ⟦(n, k)⟧) = ⟦(n, k)⟧
:= rfl
/-


# Further proofs

A non-negative integer satisfies -x = x if and only if it is zero.
-/
open Nat' in
example (n : Nat')
  (h : Z.neg ⟦(n, zero)⟧ = ⟦(n, zero)⟧)
  : n = zero
:=
  have h1 : (zero, n) ≈ (n, zero) := Quotient.exact h
  match n, h1 with
  | zero, _ => rfl
  | succ k, h2 =>
    have contradiction := calc
      zero
      _ = zero + zero := zero_add.symm
      _ = k.succ + k.succ := h2
      _ = (k.succ + k).succ := add_succ
    have : zero ≠ (k.succ + k).succ := nofun
    have : False := this contradiction
    this.rec
/-

For binary operations like addition, we use the further variant `Quotient.lift₂`, specialized here to the case where both arguments of the binary operation have the same type.
-/
example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → α → β)
  (h : ∀ (x₁ y₁ x₂ y₂ : α),
    x₁ ≈ x₂ → y₁ ≈ y₂ → f x₁ y₁ = f x₂ y₂
  ) :
  Quotient s → Quotient s → β := Quotient.lift₂ f h
/-

The variant is implemented using `Quotient.lift`.
-/
set_option pp.proofs true in
#print Quotient.lift₂._proof_2

#print Quotient.lift₂


example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → α → β)
  (h : ∀ (x₁ y₁ x₂ y₂ : α),
    x₁ ≈ x₂ → y₁ ≈ y₂ → f x₁ y₁ = f x₂ y₂
  ) :
  Quotient.lift₂ f h = λ q₁ q₂ ↦
    Quotient.lift (fun a₁ ↦ Quotient.lift (f a₁) (Quotient.lift₂._proof_1 f h a₁) q₂) (Quotient.lift₂._proof_2 f h q₂) q₁
:= rfl
/-

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
  (λ _ _ _ _ h1 h2 ↦ Quot.sound (N2.add_resp_r h1 h2))
/-

Here `Quotient.sound` is the quotient axiom.
-/
example (α : Sort u) (s : Setoid α) (a b : α) :
  a ≈ b → (Quotient.mk s a) = (Quotient.mk s b)
:= Quot.sound
/-

We can now show that `1 - 1 = 0`. Using `Quotient.sound`, it remains to show `(1, 0) + (0, 1) ≈ (0, 0)`, which reduces to `(1, 1) ≈ (0, 0)` and further to `1 + 0 = 0 + 1`. These hold by `rfl`.
-/
def Z.one : Z := ⟦(Nat'.zero.succ, Nat'.zero)⟧
def Z.minus_one : Z := ⟦(Nat'.zero, Nat'.zero.succ)⟧

open Z in
example : Z.add one minus_one = zero := Quot.sound rfl
/-

The standard integers are not defined as a quotient, and computing with them does not require using the quotient axiom.
-/
