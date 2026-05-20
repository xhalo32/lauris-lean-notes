/-
Primitives
%%%
tag := "sec-primitives"
%%%
-/
import Mathlib.Data.Nat.Init
/-
-/
-- -show
namespace Document.Primitives
/-

When used as a proof assistant, the central form of interaction with Lean is declaring a definition.{margin}[Besides `def`, its variant `example`, and `inductive`, the other commands we will encounter are the `#`-prefixed diagnostics and `set_option`, which configures them. Later we will use further variants of `def`: `abbrev`, `lemma`, and `theorem`.] The following definition gives the name `z` to `0`, and states that `z` is a natural number.{margin}[The natural numbers `0, 1,…` are denoted by `ℕ`. Hovering over `ℕ` in [VS Code][vscode] shows that it can be entered using `\N`.] {index}[def] {index}[`:`] {index}[`:=`]

[vscode]: https://lean-lang.org/install/

-/
def z : ℕ := 0
/-
In Lean, every expression has a type. While we could have chosen a name other than `z`, the kernel verifies that `0` has the type `ℕ`. We will make extensive use of a variant of `def` that omits the name and only verifies the type. {index}[example]
-/
example : ℕ := 0
/-
The following invalid example produces a type mismatch error, since the pair `(0, 1)` does not have type `ℕ`.
```lean +error
example : ℕ := (0, 1)
```

The command `#check` is used to inspect the type of an expression.{margin}[Hovering over `#check` shows its output.] {index}[#check]
-/
#check 0

#check (0, 1)
/-
The pair `(0, 1)` has type `ℕ × ℕ`, encoding the [Cartesian product][prod] of `ℕ` with itself.

[prod]: https://en.wikipedia.org/wiki/Cartesian_product

-/
example : ℕ × ℕ := (0, 1)

def p : ℕ × ℕ := (0, 1)
/-

One way in which Lean differs from many programming languages is that types are [first-class citizens][1st-class].

[1st-class]: https://en.wikipedia.org/wiki/First-class_citizen

-/
#check ℕ
/-
The type of `ℕ` is `Type`, the type universe. It is the first kernel-level primitive we have seen. In what follows, we will consider three other primitive concepts: the universe of propositions, functions, and inductive types.{margin}[The remaining primitives are used more rarely. They are {ref "sec-quotient-types"}[quotient] types and higher {ref "sec-universes"}[universes].] Natural numbers and the cartesian product are inductive types.


# Propositions
%%%
tag := "sec-propositions"
%%%

Propositions are expressions of type `Prop`, the universe of propositions.
-/
example : Prop := 0 = 0
example : Prop := 1 = 0
/-
The first proposition is provable, while the second is not.{margin}[We {ref "sec-peano"}[later] prove the negation of `1 = 0` as a consequence of the Peano axioms.] Interestingly, the proposition `0 = 0` is itself a type,{margin}[The expression `0 = 0` is syntactic sugar for `Eq 0 0`. We will {ref "sec-equality"}[return] to this later.] and an expression of type `0 = 0` encodes a proof of `0 = 0`. In general, an expression `p` of type `Prop` is itself a type. To prove `p` is to give an expression of type `p`.

The proposition `0 = 0` has a canonical proof by [reflexivity][reflexivity] of equality.{margin}[We will explain the precise meaning of `rfl` {ref "sec-equality"}[later].]

[reflexivity]: https://en.wikipedia.org/wiki/Reflexive_relation

-/
example : 0 = 0 := rfl
/-


# Definitional equality
%%%
tag := "sec-definitional-equality-naive"
%%%

In addition to enforcing the rules of the type theory, the kernel implements [definitional equality][def-eq]. If two expressions are definitionally equal, then `rfl` proves their equality, modulo elaboration-time transparency settings.{margin}[Definitions annotated as irreducible are not unfolded under default transparency. This annotation is typically used for performance reasons. The proof `by with_unfolding_all rfl` uses `rfl` under full transparency.] A sufficient condition for definitional equality is that the expressions have the same normal form.{margin}[Definitional equality has aspects beyond reduction to normal form, summarized {ref "sec-definitional-equality"}[later].] The `#reduce` command computes this normal form.{margin}[The normal form is passed through Lean's pretty-printer, a non-injective function.]

[def-eq]: https://lean-lang.org/doc/reference/latest/The-Type-System/#--tech-term-definitional-equality

-/
#reduce 1 + 1
/-
As normal form of `1 + 1` is `2`, we can use `rfl` to prove `1 + 1 = 2`.
-/
example : 1 + 1 = 2 := rfl
/-

The following example is invalid.

```lean +error
example : 1 = 0 := rfl
```


# Functions

Functions are given by $`\lambda`-abstractions. {index}[`λ … ↦`] {index}[`→`]
-/
def plus1 : ℕ → ℕ := λ n ↦ n + 1
/-
This is [syntactic sugar][sugar] for {index}[fun]

[sugar]: https://en.wikipedia.org/wiki/Syntactic_sugar

-/
def plus1₁ : ℕ → ℕ := fun n => n + 1
/-

The command `#eval` {index}[#eval] evaluates a given expression.{margin}[Parentheses are not needed in function evaluation syntax.]
-/
#eval plus1 0
/-
Lean is a proof assistant and a functional programming language. One may think of `#check` and `#eval` as reflecting these two sides. We will focus on the proof assistant features and favor a proof over `#eval`.
-/
example : plus1 0 = 1 := rfl
/-

Syntactic sugar allows for introducing the argument using parentheses. {index}[`(… : …)`]
-/
def plus1₂ (n : ℕ) : ℕ := n + 1
/-
The functions `plus1₁` and `plus1₂` coincide with `plus1`.

All functions take exactly one argument, but syntactic sugar creates the appearance of functions taking several arguments.
-/
def add : ℕ → (ℕ → ℕ) := λ n ↦ (λ m ↦ n + m)

def add₁ : ℕ → ℕ → ℕ := λ n m ↦ n + m

def add₂ (n m : ℕ) : ℕ := n + m
/-
The functions `add₁` and `add₂` coincide with `add`.


## Implication and universal quantification

In Lean, [logical implication][implication] and [universal quantification][universal-quantification] are not separate primitives but arise as function types.{margin}[Other logical connectives and existential quantification are encoded as inductive types, as seen {ref "sec-logic"}[later].]

[implication]: https://en.wikipedia.org/wiki/Logical_implication
[universal-quantification]: https://en.wikipedia.org/wiki/Universal_quantification

Implication is a function type from a proposition to a proposition. While `0 = 0` is provable and `1 = 0` is not, the following two implications are both proven by the identity function.
-/
example : 0 = 0 → 0 = 0 := λ h ↦ h

example : 1 = 0 → 1 = 0 := λ h ↦ h
/-

All natural numbers `n` satisfy `n + 1 ≠ 0`.{margin}[We will explain the proof `nofun` {ref "sec-constructor-distinct"}[later].]
-/
example (n : ℕ) : n + 1 ≠ 0 := nofun
/-
This example should be compared to `plus1₂`.{margin}[Recall that `example` is simply a variant of `def` that omits giving a name.] It states that an anonymous function taking the argument `n` yields an expression of type `n + 1 ≠ 0`. Notably, this type depends on the argument `n`. Without syntactic sugar, the example reads
-/
example : (n : ℕ) → n + 1 ≠ 0 := nofun
/-
It can also be written using syntactic sugar for universal quantification.
-/
example : ∀ n : ℕ, n + 1 ≠ 0 := nofun
/-


# Inductive types

Lean provides a substantial amount of [syntactic sugar][sugar]. Occasionally it can be useful to remove the syntactic sugar. [Pretty-printing][pretty-printing] can be adjusted using `set_option` command. {index}[`set_option`] For example, `ℕ` is syntactic sugar for {lean}`Nat`.

[pretty-printing]: https://en.wikipedia.org/wiki/Pretty-printing

-/
set_option pp.notation false in
#check ℕ
/-

The `#print` command queries information about definitions.{margin}[It does not work well with syntactic sugar.] {index}[#print]
-/
#print Nat
/-

Let us construct our first definition `z` from scratch (without syntactic sugar).
-/
inductive Nat' : Type where
  | zero : Nat'
  | succ (n : Nat') : Nat'

def z' : Nat' := Nat'.zero
/-

Expressions of type `Nat'` are put together using the
constructors `zero` and `succ`.{margin}[The constructors use the same syntax as the left-hand side of `:=` in `def`. The constructor `succ` encodes the [successor function][succ].] They are taken apart by using pattern matching. Here is the predecessor function.

[succ]: https://en.wikipedia.org/wiki/Successor_function

-/
def Nat'.pred (n : Nat') :=
  match n with
  | zero => zero
  | succ m => m
/-

Here is a proof by reflection that predecessor is the left inverse of successor.
-/
open Nat' in
example (n : Nat') : pred (succ n) = n := rfl
/-

Let us construct our second definition `p` from scratch.
-/
#print Prod

inductive Prod' (α β : Type) : Type where
  | mk (fst : α) (snd : β) : Prod' α β

def one := Nat'.succ z'

def p' : Prod' Nat' Nat' := Prod'.mk z' one
/-
The Cartesian product is parametrized by two types `α` and `β`. Pairs are put together using the only constructor `mk`.


# Further proofs

Above we made claims about certain expressions being equal. These claims can be verified using {lean}`rfl`.
-/
example : ℕ = Nat := rfl

example : (ℕ × ℕ) = (Prod Nat Nat) := rfl

example : (0 = 0) = Eq 0 0 := rfl

example : plus1 = plus1₁ := rfl
example : plus1 = plus1₂ := rfl

example : add = add₁ := rfl
example : add = add₂ := rfl

example : (∀ n : ℕ, n + 1 ≠ 0) = ((n : ℕ) → n + 1 ≠ 0)
:= rfl

example : 0 = Nat.zero := rfl
example : 1 = Nat.succ 0 := rfl

example : (0, 1) = Prod.mk 0 1 := rfl
