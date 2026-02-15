/-
Functions
-/
import Mathlib
/-
%%%
tag := "sec-functions"
%%%

A function can be written as follows. {index}[λ ... ↦]
-/
example : ℕ → ℕ := λ n ↦ n + 1
/-
The calculus of constructions is a typed [λ-calculus][lambda]. In this context, a function is given by a λ-abstraction. An alternative, less mathematical keyword `fun` {index}[fun] is also available

[lambda]: https://en.wikipedia.org/wiki/Lambda_calculus

-/
example : ℕ → ℕ := fun n => n + 1
/-
The type `ℕ → ℕ` is a function type. {index}[→] In general, `α → β` denotes a function type, with types `α` and `β` as the [domain][domain] and [codomain][codomain], respectively.

[domain]: https://en.wikipedia.org/wiki/Domain_of_a_function
[codomain]: https://en.wikipedia.org/wiki/Codomain

We can give a name to a function by replacing `example` with `def` {index}[def] and the name.
-/
def plus1 : ℕ → ℕ := λ n ↦ n + 1
/-

The command `#eval` {index}[#eval] evaluates a given expression.
-/
#eval plus1 0
/-
Parentheses are not needed in the function evaluation syntax.

Lean is a proof assistant and a functional programming language. One may think of `#check` and `#eval` as reflecting these two sides. We will focus on the proof assistant features and favor `example` over `#eval`.
-/
example : plus1 0 = 1 := rfl
/-


# Arguments

The domain can be specified by annotating the type of the argument. Then Lean can often infer the codomain.
-/
def plus1₁ := λ n : ℕ ↦ n + 1
/-

Syntactic sugar allows for introducing the argument using parentheses. {index}[`(a : α)`]
-/
def plus1₂ (n : ℕ) := n + 1
/-

Yet another way is to introduce a variable {index}[variable] in the surrounding context.
-/
variable (n : ℕ)
def plus1₃ := n + 1
/-
The functions `plus1₁`, `plus1₂`, and `plus1₃` coincide with `plus1`.


## Several arguments

Functions take exactly one argument in Lean. A function taking several arguments can be encoded as a function whose codomain is a function type.
-/
def add : ℕ → (ℕ → ℕ) := λ n ↦ (λ m ↦ n + m)
/-
For convenience, we refer to a function like this simply as a _function taking two arguments_.

Syntactic sugar creates the appearance of functions taking several arguments.
-/
def add₁ : ℕ → ℕ → ℕ := λ n m ↦ n + m
def add₂ (n : ℕ) (m : ℕ) : ℕ := n + m
def add₃ (n m : ℕ) : ℕ := n + m
/-

We can also make use of the variable `n` that we defined above.
-/
def add₄ (m : ℕ) : ℕ := n + m
/-
The functions `add₁, ..., add₄` coincide with `add`.

[Partial application][partial-application] produces a function taking the remaining arguments.

[partial-application]: https://en.wikipedia.org/wiki/Partial_application

-/
def plus1' : ℕ → ℕ := add 1
/-

The following function taking two arguments ignores the second one. {index}[_]
-/
def proj : ℕ → ℕ → ℕ := λ n ↦ λ _ ↦ n

example : proj 0 1 = 0 := rfl
/-


## Types as arguments
%%%
tag := "sec-functions-of-types"
%%%

{ref "sec-expressions"}[Recall] that `Prod ℕ ℕ` gives the Cartesian product. {lean}`Prod` is a function whose arguments and values are types.
-/
example : Type → Type → Type := Prod
/-

In fact, {lean}`Prod` is a more general [universe-polymorphic][univ-polymorphic] function. The general version can be written with the help of [universe variables][univ-variable]. {index}[universe]

[univ-polymorphic]: https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/#--tech-term-universe-polymorphism
[univ-variable]: https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=The-Lean-Language-Reference--The-Type-System--Universes--Polymorphism--Universe-Variable-Bindings

-/
universe u v

example : Type u → Type v → Type (max u v) := Prod
/-
We will return to the least upper bound appearing in the codomain.

Here are some variations
-/
def Prod₁ (t : Type) (s : Type) : Type := Prod t s
def Prod₂ : Type → Type → Type := Prod
def Prod₃ : Type → Type → Type := λ t ↦ λ s ↦ t × s
def Prod₄ (t s : Type) : Type := t × s
/-
The functions `Prod₁, ..., Prod₄` all coincide with {lean}`Prod`, though, they are instantiated with a fixed level of the type hierarchy.


## Implicit arguments

{ref "sec-definitional-equality-naive"}[Recall] that {lean}`rfl` {index}[rfl] can be viewed as a canonical proof of `a = a` for any expression `a`. In fact, {lean}`rfl` is a function taking two implicit arguments.
-/
#check rfl
/-
Implicit arguments {index}[`{a : α}`] are written using curly braces `{...}` instead of parentheses `(...)`. Lean infers their values from context.
-/
example {α : Sort u} {a : α} : a = a := rfl
/-

Inference of implicit arguments can be disabled using `@`. {index}[@]
-/
example (α : Sort u) (a : α) : a = a := @rfl α a
example : (α : Sort u) → (a : α) → a = a := @rfl
/-
The explicit version `@rfl` bears some similarity with `Prod`, see in particular `Prod₁` and `Prod₂`. It is a function taking two arguments: first a type `α`, and then an expression `a` of that type. The codomain `a = a` of `@rfl` depends on the arguments.


# Dependent function types
%%%
tag := "sec-dependent-function-types"
%%%

To simplify the notation, we introduce the following shorthand.
-/
variable {I : Type}
def X (i : I) := i = i
/-

Consider the following partially applied version of `@rfl`.
-/
example : (i : I) → X i := @rfl I
/-
The type of `@rfl I` is a dependent function type, also called a [Π-type][Pi-type]. Such a type can be thought of as denoting an [indexed product][indexed-product] of sets.

[Pi-type]: https://en.wikipedia.org/wiki/Dependent_type#%CE%A0_type
[indexed-product]: https://en.wikipedia.org/wiki/Cartesian_product#Infinite_Cartesian_products

In fact, all function types are Π-types.
-/
example
  (α : Sort u) (β : Sort v) : (α → β) = ((_ : α) → β)
:= rfl
/-

In the case of `plus1` and `Prod`, the codomains do not depend on the arguments.
-/
example : (_ : ℕ) → ℕ := plus1
example : (_ : Type) → ((_ : Type) → Type) := Prod
/-


# Implication

Implication is expressed using function types in the universe of propositions, in line with the [Curry–Howard correspondence][CH-correspondence].

[CH-correspondence]: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

-/
example (p q : Prop) : Prop := p → q
example : Prop → Prop → Prop := λ p ↦ λ q ↦ p → q
/-

{ref "sec-propositions"}[Recall] that a proof of a proposition is an expression having the proposition as its type. [Modus ponens][modus-ponens] has a natural proof by composition. We give two formulations.

[modus-ponens]: https://en.wikipedia.org/wiki/Modus_ponens

-/
example (p q : Prop) (h1 : p → q) (h2 : p) : q := h1 h2

example
  (p q : Prop) : (p → q) → p → q
:=
  λ h1 ↦ λ h2 ↦ h1 h2
/-


# Universal quantification

As with implication, universal quantification is expressed using dependent function types in the universe of propositions.

The following proposition expresses that the predicate `P x` holds for all `x` of type `s`.
-/
example (s : Sort u) (P : s → Prop) : Prop := (x : s) → P x
/-

Convenient syntactic sugar is provided.
-/
example
  (s : Sort u) (P : s → Prop)
  : (∀ x : s, P x) = ((x : s) → P x)
:= rfl
/-

Here is a natural proof of "pointwise" modus ponens using function application and composition.
-/
example (s : Sort u) (P Q : s → Prop)
  (h1 : ∀ x : s, P x → Q x) (h2 : ∀ x : s, P x)
  : ∀ x : s, Q x
:= λ x ↦ h1 x (h2 x)
/-

Recall that `@rfl` has the following type.
-/
example : (α : Sort u) → (a : α) → a = a := @rfl
/-
It can be rewritten using universal quantification.
-/
example : ∀ α : Sort u, ∀ a : α, a = a := @rfl
example : ∀ (α : Sort u) (a : α), a = a := @rfl
/-


# Function extensionality

The functions `plus1` and `plus1'` coincide in the sense that they give the same value when applied to the same argument, that is, they are [extensionally][extensionality] equal. However, they are not definitionally equal, because the two terms in the addition are in the opposite orders in their definitions.

[extensionality]: https://lean-lang.org/doc/reference/latest/The-Type-System/Functions/#function-extensionality

-/
example : plus1 =  (λ n ↦ n + 1) := rfl
example : plus1' = (λ n ↦ 1 + n) := rfl
/-

The following invalid line of code produces a type mismatch error.

```lean +error
example : plus1 = plus1' := rfl
```

Function extensionality is available in Lean as a theorem called {lean}`funext`. We can show that `plus1` and `plus1'`are indeed equal.
-/
example : plus1 = plus1' := by
  funext n
  simp [plus1, plus1', add]
  grind
/-
We will explain how to write proofs like this in due course. For the moment, we simply record that the principle of [functional extensionality][extensionality-principles] holds in Lean.

[extensionality-principles]: https://en.wikipedia.org/wiki/Extensionality#Extensionality_principles


# Local definitions

Consider the following function.
-/
def pq (x : ℕ) : ℕ :=
  (x + 1)^2 + 3*(x + 1) + 1
/-

We can define the same function by using a local definition with `let` {index}[let].
-/
def pq₁ (x : ℕ) : ℕ :=
  let y := x + 1
  y^2 + 3*y + 1
/-

Another alternative is to introduce two auxiliary functions.
-/
def q (x : ℕ) : ℕ := x + 1
def p (y : ℕ) : ℕ := y^2 + 3*y + 1
def pq₂ := p ∘ q
/-
Here `∘` is the [function composition][comp], syntactic sugar for {lean}`Function.comp`. A local definition is a [syntactic abbreviation][local-def], and there are cases where it works but the composition does not.

[comp]: https://en.wikipedia.org/wiki/Function_composition
[local-def]: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#local-definitions

-/
def plus1₄ :=
  let t := ℕ
  λ x : t ↦ x + 1
/-


# Reductions of beta, delta, and zeta kind

{ref "sec-definitional-equality-naive"}[Recall] that having the same normal form is a sufficient condition for two expressions to be definitionally equal. Computing normal forms involves several kinds of reduction, three of which are related to the concepts introduced in this section.


## beta-reduction

β-reduction corresponds to applying a function to an argument by substitution.

-/
variable (α β : Type) (f : α → β) (a : α)

example : (λ x ↦ f x) a = f a := rfl

#reduce (λ x ↦ f x) a
#reduce f a
/-


## delta-reduction

δ-reduction replaces a defined name{margin}[Names of expressions are referred to as constants in the Lean Language Reference, see for example [Definitions][definitions] there.] by its defining expression.

[definitions]: https://lean-lang.org/doc/reference/latest/Definitions/Definitions/#The-Lean-Language-Reference--Definitions--Definitions

While we have so far used `def` only to give names to functions, any expression can be named.
-/
def ℕ2 := ℕ × ℕ

example : ℕ2 = (ℕ × ℕ) := rfl

#reduce (types := true) ℕ2
#reduce (types := true) ℕ × ℕ
/-

One might ask why we do not use a previously defined name such as `plus1`. The reason is that `#reduce plus1` does not demonstrate δ-reduction in isolation, as can be observed by comparing the normal form and definition of `plus1`.
-/
#reduce plus1
#print plus1
/-
The normal form of `plus1` is related to the inductive definition of ℕ, which we explain in the next section.


## zeta-reduction

ζ-reduction eliminates a local definition by substitution.

{index}[;]
-/
example : (let t := ℕ; t × t) = (ℕ × ℕ) := rfl

#reduce (types := true) (let t := ℕ; t × t)
/-
The semicolon is a syntactic device that allows multiple expressions to be written on a single line. Replacing it by a line break leaves the expression intact.


# Function eta-equivalence
%%%
tag := "sec-function-eta-equivalence"
%%%

In addition to reduction, definitional equality identifies certain expressions that differ only by trivial abstraction. This identification is called η-equivalence.

For functions, η-equivalence says that a function is definitionally equal to the λ-abstraction obtained by applying the function to an argument.
-/
example : (λ x ↦ f x) = f := rfl
/-
The definitional equality of the left and right-hand sides is not based on them having the same normal form. In fact, their normal forms differ, as can be observed using `#reduce`.
-/
#reduce λ x ↦ f x
#reduce f
/-

Reduction and η-equivalence differ in a fundamental way: the former has an [intensional][intensional-extensional] nature while the latter is a limited kind of extensionality.

[intensional-extensional]: https://en.wikipedia.org/wiki/Extensional_and_intensional_definitions


# Surface syntax and underlying type theory

Lean's processing of source code can be divided into several [stages][processing-stages]. For our purposes, the important stages are:

[processing-stages]: https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/

* _Macro expansion_ that replaces syntactic sugar with more basic syntax.
* _Elaboration_ that translates user-facing surface syntax into expressions of type theory.
* _Kernel checking_ that ensures that the simplified expressions follow the rules of the type theory.

The type theory is designed to be simple, enabling the trusted kernel to remain small. From a foundational perspective, trusting Lean means trusting the correctness of this small kernel. In addition to enforcing the rules of the type theory, the trusted kernel implements definitional equality, which accounts for η-equivalence as well as β-, δ-, and ζ-reductions, together with ι-reduction that we describe {ref "sec-iota-reduction"}[later].

Implicit and explicit arguments do not differ at the level of the type theory, only during elaboration. For example, at the level of the type theory, `rfl` is simply a function taking two arguments.
-/
example (α : Sort u) (a : α) : a = a := rfl
/-


# Further proofs

-/
example : plus1 = (λ n ↦ n + 1) := rfl
example : plus1 = plus1₁ := rfl
example : plus1 = plus1₂ := rfl
example : plus1 = plus1₃ := rfl
example : plus1 = plus1₄ := rfl

example : (ℕ → (ℕ → ℕ)) = (ℕ → ℕ → ℕ) := rfl

example : add = (λ n m ↦ n + m) := rfl
example : add = add₁ := rfl
example : add = add₂ := rfl
example : add = add₃ := rfl
example : add = add₄ := rfl

example : Prod = Prod₁ := rfl
example : Prod = Prod₂ := rfl
example : Prod = Prod₃ := rfl
example : Prod = Prod₄ := rfl

example :
  ((α : Sort u) → (a : α) → a = a)
  = (∀ α : Sort u, ∀ a : α, a = a)
:= rfl
example :
  ((α : Sort u) → (a : α) → a = a)
  = (∀ (α : Sort u) (a : α), a = a)
:= rfl

example : pq = pq₁ := rfl
example : pq = pq₂ := rfl
