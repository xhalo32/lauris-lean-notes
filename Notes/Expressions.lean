/-
Expressions, types and propositions
-/
import Mathlib
/-
%%%
tag := "sec-expressions"
%%%

Lean is based on a _type theory_ that is a version of the [calculus of constructions][coc] with [inductive types][inductive-type]. In particular, every expression has a type. The `example` {index}[example] command checks that a given expression has the specified type.

[coc]: https://en.wikipedia.org/wiki/Calculus_of_constructions
[inductive-type]: https://en.wikipedia.org/wiki/Inductive_type

-/
example : ℕ := 0
/-
In this case, the expression is `0` and the type is {lean}`ℕ`. (The type precedes the expression for a reason that will become clear as we move forward.) The example asserts that the expression `0` has type ℕ, denoting the natural numbers, which are also written as {lean}`Nat`. Using programming jargon, we say that ℕ is [syntactic sugar][sugar]{margin}[In [VS Code][vscode], you can hover over ℕ and other non-ascii characters to see how they can be typed.] for {lean}`Nat`.

[vscode]: https://marketplace.visualstudio.com/items?itemName=leanprover.lean4
[sugar]: https://en.wikipedia.org/wiki/Syntactic_sugar

The command `#check` {index}[#check] is used to inspect{margin}[You can hover over `#check` to see its output] the type of an expression. It is useful when learning, debugging, or exploring how Lean interprets expressions.
-/
#check 0
/-
The output `0 : ℕ` means that `0` has type `ℕ`. We will occasionally use this notation in our explanations.

-/
#check (0, 1)
/-
The pair `(0, 1)` has type `ℕ × ℕ`, standing for the [Cartesian product][prod] of ℕ with itself. This is syntactic sugar for `Prod ℕ ℕ`.

[prod]: https://en.wikipedia.org/wiki/Cartesian_product

-/
example : ℕ × ℕ := (0, 1)
/-

The following invalid line of code produces a type mismatch error since the pair `(0, 0)` doesn't have type `ℕ`.

```lean +error
example : ℕ := (0, 0)
```


# Types as expressions

One way in which Lean differs from many other programming languages is that types themselves are expressions.
-/
example : ℕ := 0
example : Type := ℕ
/-
That is, `0` has type `ℕ`, and `ℕ` has type {lean}`Type`. Also,
-/
example : Type := ℕ × ℕ
/-

Using programming jargon, it could be said that types are [first-class citizens][1st-class].
But {lean}`Type` is also a type, so what's its type?

[1st-class]: https://en.wikipedia.org/wiki/First-class_citizen

-/
example : Type 1 := Type
/-

In fact, there is an infinite hierarchy of types,
-/
example : Type 2 := Type 1
example : Type 3 := Type 2
/-
and so on. {lean}`Type` is an abbreviation for {lean}`Type 0`.


# Propositions
%%%
tag := "sec-propositions"
%%%

Propositions are expressions of type {lean}`Prop`.
-/
example : Prop := 0 = 0
example : Prop := 0 = 1
/-
The first proposition is provable, while the second is not. In fact, the negation of the second is provable.

Just like `ℕ`, {lean}`Prop` has type {lean}`Type`.
-/
example : Type := Prop
/-

Interestingly, `0 = 0` is a type. An expression of type `0 = 0` is a proof of `0 = 0`. In other words, to prove a proposition in Lean is to construct an expression having the proposition as its type.
-/
example : 0 = 0 := rfl
/-
We will consider the precise meaning of {lean}`rfl` {index}[rfl] (and `=`) later. For the moment, let's just view {lean}`rfl` as a canonical proof of `a = a` for any expression `a`.

The [right shift][right-shift] of the type hierarchy, with `Prop` at level `0`, is called the universe hierarchy `Sort u`,
indexed by `u = 0, 1, ...`. Thus, `Prop` abbreviates `Sort 0`, while `Type u` abbreviates `Sort (u + 1)`. This is the full hierarchy used by Lean.

[right-shift]: https://en.wikipedia.org/wiki/Shift_operator#Sequences


# Definitional equality
%%%
tag := "sec-definitional-equality-naive"
%%%

If two expressions are [definitionally equal][def-eq], their equality can be proven using {lean}`rfl`.
Having the same normal form is a sufficient (but not necessary) condition for definitional equality. In the following example, the left and right-hand sides have the same normal form.
-/
example : 0 = 1 - 1 := rfl
/-

[def-eq]: https://lean-lang.org/doc/reference/latest/The-Type-System/#--tech-term-definitional-equality

The `#reduce` {index}[#reduce] command displays the normal form of an expression.
-/
#reduce 1 - 1
/-
We will explain the different kinds of reduction used by `#reduce` in due course.

By default, `#reduce` does not reduce inside types. This affects equality, since an equality `a = a` is itself a type, namely `Eq a a`. We will return to this later.
-/
#reduce 0 = 1 - 1
/-

We can force the reduction using the `types := true` option.
-/
#reduce (types := true) 0 = 1 - 1
/-

The following invalid line of code produces a type mismatch error.

```lean +error
example : 0 = 1 := rfl
```


# Further proofs

Above we made claims about certain expressions being equal. These claims can be verified using {lean}`rfl`.

-/
example : ℕ = Nat := rfl

example : (ℕ × ℕ) = (Prod ℕ ℕ) := rfl

example : Type = Type 0 := rfl
example : Type 0 = Sort 1 := rfl
example : Type 1 = Sort 2 := rfl
example : Prop = Sort 0 := rfl

example : (0 = 0) = Eq 0 0 := rfl
/-

After declaring a universe variable, we can verify the relation between the type and universe hierarchies in general. We will {ref "sec-functions-of-types"}[return] to universe variables.
-/
universe u

example : Type u = Sort (u + 1) := rfl
