/-
Types, propositions and universes
%%%
tag := "sec-expressions"
%%%
-/
import Mathlib.Data.Nat.Init
/-
Lean is based on a typed [$`\lambda`-calculus][lambda], specifically a version of the [calculus of constructions][coc] with [inductive types][inductive-types]. We will refer to this formal system simply as _type theory_. In particular, every expression has a type. The `example` {index}[example] command checks that a given expression has the specified type.{margin}[Hovering over `ℕ` in [VS Code][vscode] shows that it can be entered using `\N`.]

[lambda]: https://en.wikipedia.org/wiki/Lambda_calculus
[coc]: https://en.wikipedia.org/wiki/Calculus_of_constructions
[inductive-types]: https://en.wikipedia.org/wiki/Inductive_type

{index}[`:=`]
-/
example : ℕ := 0
/-
The example asserts that `ℕ` is the type of `0`. The type `ℕ` encodes the natural numbers. The command `#check` {index}[#check] is used to inspect the type of an expression.{margin}[Hovering over `#check` shows its output.]

[vscode]: https://lean-lang.org/install/

-/
#check 0
/-
The output `0 : ℕ` means that `0` has type `ℕ`. Another way to say this is that `0` inhabits `ℕ`.

Lean provides a substantial amount of [syntactic sugar][sugar] and more general user-facing surface syntax. When studying the underlying type theory, it can be useful to consider expressions from which the surface syntax has been removed. [Pretty-printing][pretty-printing] can be adjusted using `set_option` command. {index}[`set_option`] For example, `ℕ` is syntactic sugar for {lean}`Nat`.

[sugar]: https://en.wikipedia.org/wiki/Syntactic_sugar
[pretty-printing]: https://en.wikipedia.org/wiki/Pretty-printing

-/
set_option pp.notation false in
#check 0
/-

The pair `(0, 1)` has type `ℕ × ℕ`, encoding the [Cartesian product][prod] of `ℕ` with itself. This is syntactic sugar for `Prod Nat Nat`.

[prod]: https://en.wikipedia.org/wiki/Cartesian_product

-/
#check (0, 1)

example : Prod Nat Nat := (0, 1)
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
The first proposition is provable, while the second is not.{margin}[In fact, the negation of `1 = 0` is a consequence  the Peano axioms that we prove {ref "sec-peano"}[later]] Interestingly, the proposition `0 = 0` is itself a type,{margin}[The expression `0 = 0` is syntactic sugar for `Eq 0 0`. We will {ref "sec-equality"}[return] to this later.] and an expression of type `0 = 0` encodes a proof of `0 = 0`. In general, all expressions of type {lean}`Prop` are themselves types. To prove a proposition in Lean is to construct an expression inabiting the proposition.
-/
example : 0 = 0 := rfl
/-
We will consider the precise meaning of {lean}`rfl` {ref "sec-equality"}[later]. For the moment, let us simply view {lean}`rfl` as a canonical proof of [reflexivity][reflexivity] of equality.

[reflexivity]: https://en.wikipedia.org/wiki/Reflexive_relation

Like `ℕ`, {lean}`Prop` inhabits {lean}`Type`.
-/
example : Type := Prop
/-


# Definitional equality
%%%
tag := "sec-definitional-equality-naive"
%%%

If two expressions are [definitionally equal][def-eq], then their equality can be proven using {lean}`rfl`. A sufficient (but not necessary) condition for definitional equality is that the expressions have the same normal form. The `#reduce` {index}[#reduce] command displays this normal form.{margin}[Further details of the reduction to normal form will be provided in due course. A {ref "sec-definitional-equality"}[summary] covering all aspects of definitional equality is also available.]

[def-eq]: https://lean-lang.org/doc/reference/latest/The-Type-System/#--tech-term-definitional-equality

-/
#reduce 1 - 1
/-
Since the normal form of `1 - 1` is `0`, we can use {lean}`rfl` to prove `1 - 1 = 0`.
-/
example : 1 - 1 = 0 := rfl
/-

By default, `#reduce` does not reduce inside types. This matters for equality, since it is itself a type.
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

The infinite sequence `Prop, Type 0, Type 1, …` is syntactic sugar for the universe hierarchy `Sort 0, Sort 1, Sort 2, …`. Here `Sort u` is called a universe and `u` is its level. We can verify that the two sequences coincide using {lean}`rfl`.
-/
example : Prop = Sort 0 := rfl
example : Type u = Sort (u + 1) := rfl
/-

The type of a universe is the next universe in the hierarchy.
-/
example : Sort (u + 1) := Sort u
/-

Each type `α` inhabits `Sort u` for exactly one `u = 0, 1, …`. We say that this `Sort u` is the universe of `α`.


# Further proofs

Above we made claims about certain expressions being equal. These claims can be verified using {lean}`rfl`.

-/
example : ℕ = Nat := rfl

example : (ℕ × ℕ) = (Prod ℕ ℕ) := rfl

example : Type = Type 0 := rfl

example : (0 = 0) = Eq 0 0 := rfl
