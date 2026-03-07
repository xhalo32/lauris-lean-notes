/-
Types, propositions and universes
%%%
tag := "sec-expressions"
%%%
-/
import Mathlib
/-
Lean is based on a typed [$`\lambda`-calculus][lambda], specifically a version of the [calculus of constructions][coc] with [inductive types][inductive-types]. We will refer to this formal system simply as _type theory_. In particular, every expression has a type. The `example` {index}[example] command checks that a given expression has the specified type.

[lambda]: https://en.wikipedia.org/wiki/Lambda_calculus
[coc]: https://en.wikipedia.org/wiki/Calculus_of_constructions
[inductive-types]: https://en.wikipedia.org/wiki/Inductive_type

{index}[`:=`]
-/
example : ℕ := 0
/-
The example asserts that `ℕ` is the type of `0`. The type `ℕ` encodes the natural numbers.{margin}[Hovering over `ℕ` in [VS Code][vscode] shows that it can be entered using `\N`.]

Lean provides a substantial amount of [syntactic sugar][sugar]. For example, `ℕ` is syntactic sugar for {lean}`Nat`. Understanding the underlying type theory often requires considering expressions from which syntactic sugar has been removed.

[vscode]: https://lean-lang.org/install/
[sugar]: https://en.wikipedia.org/wiki/Syntactic_sugar

The command `#check` {index}[#check] is used to inspect the type of an expression.{margin}[Hovering over `#check` shows its output.]
-/
#check 0
/-
The output `0 : ℕ` means that `0` has type `ℕ`. Another way to say this is that `0` inhabits `ℕ`.

-/
#check (0, 1)
/-
The pair `(0, 1)` has type `ℕ × ℕ`, encoding the [Cartesian product][prod] of `ℕ` with itself. This is syntactic sugar for `Prod ℕ ℕ`.

[prod]: https://en.wikipedia.org/wiki/Cartesian_product

-/
example : ℕ × ℕ := (0, 1)
/-

The following invalid example produces a type mismatch error, since the pair `(0, 0)` does not have type `ℕ`.

```lean +error
example : ℕ := (0, 0)
```


# Types as expressions

One way in which Lean differs from many other programming languages is that types are [first-class citizens][1st-class].

[1st-class]: https://en.wikipedia.org/wiki/First-class_citizen

-/
example : ℕ := 0
example : Type := ℕ
/-
That is, `0` has type `ℕ`, and `ℕ` has type {lean}`Type`. Also,
-/
example : Type := ℕ × ℕ
/-

Like all types, {lean}`Type` has a type.
-/
example : Type 1 := Type
/-

In fact, there is an infinite sequence of types,
-/
example : Type 2 := Type 1
example : Type 3 := Type 2
/-
and so on. {lean}`Type` is an abbreviation for `Type 0`; in fact, both are syntactic sugar, as we will explain shortly.


# Propositions
%%%
tag := "sec-propositions"
%%%

Propositions are expressions of type {lean}`Prop`.
-/
example : Prop := 0 = 0
example : Prop := 1 = 0
/-
The first proposition is provable, while the second is not. In fact, the negation of the second is provable.

Interestingly, the proposition `0 = 0` is itself a type. In general, all expressions of type {lean}`Prop` are themselves types.

An expression of type `0 = 0` is viewed as a proof of `0 = 0`. In general, to prove a proposition in Lean is to construct an expression having the proposition as its type.
-/
example : 0 = 0 := rfl
/-
We will consider the precise meaning of {lean}`rfl` (and the equality `=`) {ref "sec-equality"}[later]. For the moment, let us simply view {lean}`rfl` as a canonical proof of `a = a` for any expression `a`.

Like `ℕ`, {lean}`Prop` has type {lean}`Type`.
-/
example : Type := Prop
/-


# Definitional equality
%%%
tag := "sec-definitional-equality-naive"
%%%

If two expressions are [definitionally equal][def-eq], then their equality can be proven using {lean}`rfl`. A sufficient (but not necessary) condition for definitional equality is that the expressions have the same normal form; the `#reduce` {index}[#reduce] command displays this normal form.{margin}[Further details of the reduction to normal form will be provided in due course. A {ref "sec-definitional-equality"}[summary] covering all aspects of definitional equality is also available.]

[def-eq]: https://lean-lang.org/doc/reference/latest/The-Type-System/#--tech-term-definitional-equality

-/
#reduce 1 - 1
/-
Since the normal form of `1 - 1` is `0`, we can use {lean}`rfl` to prove `1 - 1 = 0`.
-/
example : 1 - 1 = 0 := rfl
/-

By default, `#reduce` does not reduce inside types. This matters for equality, since an expression such as `a = a` is itself a type, namely `Eq a a`. We will {ref "sec-equality"}[return] to this later.
-/
#reduce 1 - 1 = 0
/-

We can force reduction inside types as follows.
-/
#reduce (types := true) 1 - 1 = 0
/-

The following example is invalid.

```lean +error
example : 1 = 0 := rfl
```


# Universe hierarchy

The infinite sequence `Prop, Type 0, Type 1, …` is syntactic sugar for the universe hierarchy `Sort 0, Sort 1, Sort 2, …`. Here `Sort u` is called a universe and `u` is its level.

We can verify that the two sequences coincide using {lean}`rfl`.
-/
example : Prop = Sort 0 := rfl
example : Type u = Sort (u + 1) := rfl
/-

The type of a universe is the next universe in the hierarchy.
-/
example : Sort (u + 1) := Sort u
/-

Each type `α` satisfies `α : Sort u` for exactly one `u = 0, 1, …`. We say that `Sort u` is the universe of `α` or that `α` inhabits `Sort u`.


# Further proofs

Above we made claims about certain expressions being equal. These claims can be verified using {lean}`rfl`.

-/
example : ℕ = Nat := rfl

example : (ℕ × ℕ) = (Prod ℕ ℕ) := rfl

example : Type = Type 0 := rfl

example : (0 = 0) = Eq 0 0 := rfl
