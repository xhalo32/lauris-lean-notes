/-
Functions
%%%
tag := "sec-functions"
%%%
-/
--import Mathlib.Data.Nat.Init
import Mathlib
import Counterexamples.Girard
/-
-/
-- -show
namespace Document.Functions
/-
We consider a sublanguage that is a [pure type system][pure-type-system]. A pure type system is defined by its universes, the relations between the universes, and a number of rules. The rules govern

[pure-type-system]: https://en.wikipedia.org/wiki/Pure_type_system

* formation: how a type is created
* introduction: how expressions of a type are created
* elimination: how expressions of a type are transformed to expressions of another type
* reduction: how introduction and elimination interact

In the case of Lean, a further category is useful:

* equality: which expressions of a type are equal

These organizational categories are applied here to functions. We later apply them to inductive types and quotient types.


# Preliminaries

To understand the formation rule for function types, we must first consider the universes and the relations between them. We introduce also proof irrelevance, since it lies behind an exceptional case of the rule.


## Proof irrelevance

If `a` has type `α`, we say that `a` inhabits `α` and that `α` is inhabited. Recall that `Prop` is the universe of propositions. Each expression inhabiting `Prop` is a type encoding a proposition, and proving a proposition amounts to giving an expression inhabiting the proposition. We call an expression inhabiting a proposition a proof.

Definitional equality includes proof irrelevance: any two proofs of the same proposition are equal.
-/
example (p : Prop) (pf₁ pf₂ : p) : pf₁ = pf₂ := rfl
/-


## Universes
%%%
tag := "sec-universes"
%%%


The universe of propositions `Prop` inhabits the type universe `Type`.
-/
example : Type := Prop
/-
`Type` itself inhabits a type.
-/
example : Type 1 := Type
/-
In fact, there is an infinite sequence of type universes,
-/
example : Type 2 := Type 1
example : Type 3 := Type 2
/-
and so on. `Type` is an abbreviation for `Type 0`.
-/
example : Type = Type 0 := rfl
/-

The infinite sequence `Prop, Type 0, Type 1, …` is syntactic sugar for the universe hierarchy `Sort 0, Sort 1, Sort 2, …`. Here `Sort u` is called a universe and `u` is its level. We can verify that the two sequences coincide using {lean}`rfl`.
-/
example : Prop = Sort 0 := rfl
example : Type u = Sort (u + 1) := rfl
/-


## Relations between universes

A pure type system comes with a relation on its universes specifying which universes inhabit each other. In the case of Lean this relation is fully described by
-/
example : Sort (u + 1) := Sort u
/-
Each universe inhabits the next one and no others.

More generally, each type `α` inhabits `Sort u` for exactly one `u`. We say that this `Sort u` is the universe of `α`.


# Formation
%%%
tag := "sec-functions-formation"
%%%

An elementary function type is formed as follows.
-/
example (α β : Type) : Type := α → β
/-
Here the types `α` and `β` specify the [domain][domain] and [codomain][codomain], respectively. The operator `→` is [right-associative][right-associative], that is,

[domain]: https://en.wikipedia.org/wiki/Domain_of_a_function
[codomain]: https://en.wikipedia.org/wiki/Codomain
[right-associative]: https://en.wikipedia.org/wiki/Operator_associativity
-/
example (α β γ : Type) : (α → β → γ) = (α → (β → γ)) := rfl
/-
This is often viewed as encoding functions that take two arguments, the first in `α` and the second in `β`, and yield a result in `γ`. We refer to `γ` as the _final codomain_. Moreover, we say that the final codomain of a type `δ` is `δ` itself whenever `δ` is not a function type.{margin}[This unified terminology across all types is used for instance when discussing {ref "sec-inductive-type-formation"}[type constructors] and {ref "sec-well-formedness"}[well-formedness requirements] of inductive types.]

{ref "sec-intro-logic"}[Recall] that the codomain of a function may depend on its argument. Consider the following abstract example.
-/
example (I : Type) (X : I → Type) : Type := (i : I) → X i
/-
We refer to `(i : I) → X i` as a [$`\Pi`-type][pi-type].{margin}[$`\Pi`-types are also called dependent function types.]  Such a type can be thought of as encoding an [indexed product][indexed-product] of sets,
$$`
\prod_{i \in I} X_i
=
\left\{\left. f: I \to \bigcup_{i \in I} X_i\ \right|
\ f(i) \in X_i,\ i \in I \right\}.
`

[pi-type]: https://en.wikipedia.org/wiki/Dependent_type#%CE%A0_type
[indexed-product]: https://en.wikipedia.org/wiki/Cartesian_product#Infinite_Cartesian_products

In fact, all function types are $`\Pi`-types. In the elementary case discussed above, the codomain simply does not depend on the argument.
-/
example
  (α : Sort u) (β : Sort v) : (α → β) = ((a : α) → β)
:= rfl
/-
Since `a` does not appear in the codomain, we can rewrite the type leaving it as a hole. {index}[`_`]
-/
example
  (α : Sort u) (β : Sort v) : (α → β) = ((_ : α) → β)
:= rfl
/-


## Impredicative maximum rule
%%%
tag := "sec-impredicative-lub-rule"
%%%

The formation of a $`\Pi`-type is governed by the following _impredicative maximum rule_.{margin}[This name is not used in the Lean Language Reference; the rule itself is described in [Predicativity][predicativity]. The [level expression][level-expression] `imax u v` is called the impredicative maximum (or least upper bound) of `u` and `v`. We have named the rule accordingly.]

[predicativity]: https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/#The-Lean-Language-Reference--The-Type-System--Universes--Predicativity
[level-expression]: https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/?terms=imax#level-expressions

-/
def imax_rule (I : Sort u) (X : I → Sort v) :
  Sort (imax u v) := (i : I) → X i
/-
where
-/
example : Sort (imax _ 0) = Sort 0 := rfl

example : Sort (imax u (v + 1)) = Sort (max u (v + 1))
:= rfl
/-

Consider the implication.
-/
example (p : Prop) (q : Prop) : Prop := p → q
/-
The type `Prop` of `p → q` arises from the impredicative maximum rule. Indeed, since
-/
example (p : Prop) : Sort 0 := p
example (q : Prop) : Sort 0 := q
/-
the rule applies with `u = 0` and `v = 0`, yielding the type
-/
example : Sort (imax 0 0) = Prop := rfl
/-

Let us now consider universal quantification.
-/
example
  (α : Sort u) (P : α → Prop)
  : (∀ a : α, P a) = ((a : α) → P a)
:= rfl
/-
The type of predicates on `α` satisfies
-/
example (α : Sort u) : Sort (max u 1) := α → Prop
/-
Here `Sort (max u 1)` arises from the impredicative maximum rule. Indeed, since
-/
example : Sort 1 := Prop
/-
the rule applies with `v = 1`, yielding `Sort (max u 1)`. The universal quantification, on the other hand, is a proposition.
-/
example (α : Sort u) (P : α → Prop) : Prop := (a : α) → P a
/-
Here `Prop` arises from the impredicative maximum rule. Indeed, since the evaluation `P a` of a predicate is a proposition,
-/
example (α : Sort u) (P : α → Prop) (a : α) : Sort 0 := P a
/-
the rule applies with `v = 0` yielding
-/
example : Prop = Sort (imax _ 0) := rfl
/-


## Implicit arguments

We have used extensively `rfl`. It is a function taking two implicit arguments. Implicit arguments  are written using curly braces. {index}[`{… : …}`]
-/
example : {α : Sort u} → {a : α} → a = a := rfl
/-
The first argument is a type `α`, and the second is an expression `a` of that type. The final codomain `a = a` depends on the arguments. The implicit arguments can be inferred from it due to this dependence. In general, implicit arguments are translated into their explicit counterparts during elaboration.

Prefixing a function with `@` makes all its implicit arguments explicit. {index}[`@`]
-/
example : (α : Sort u) → (a : α) → a = a := @rfl

example (α : Sort u) (a : α) : a = a := @rfl α a
/-


## Universe polymorphism

The function `rfl` is [universe-polymorphic][univ-polymorphic]: it depends on a universe level, denoted by `u` in the following example.

[univ-polymorphic]: https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/#--tech-term-universe-polymorphism

-/
example : (α : Sort u) → (a : α) → a = a := @rfl
/-

A universe-polymorphic function can be instantiated at fixed universe levels.
-/
example : (α : Type) → (a : α) → a = a := @rfl

example : (α : Prop) → (a : α) → a = a := @rfl
/-

If a name depends on universe levels, diagnostic output shows them in curly braces after the name, with a dot in between.
-/
#check rfl
/-


## Girard's paradox
%%%
tag := "sec-girard"
%%%

The impredicative maximum rule relies on the infinite sequence of universes as seen by considering the function type with the same universe as domain and codomain.
-/
def pi : Type (w + 1) := Type w → Type w
/-
Having an infinite number of universes is not a feature introduced by choice, rather it is the price of consistency. [Certain historical][system-U] pure type systems that lack sufficient stratification are inconsistent.

[system-U]: https://en.wikipedia.org/wiki/System_U

In Lean, violating the impredicative maximum rule would lead to Girard's paradox, formulated as follows.
-/
example
  (π : (Type w → Type w) → Type w)
  (Λ : {ξ : Type w → Type w} → ((i : Type w) → ξ i) → π ξ)
  (app : {ξ : Type w → Type w} → π ξ → (i : Type w) → ξ i)
  (β : ∀
    {ξ : Type w → Type w}
    (f : (i : Type w) → ξ i)
    (x : Type w),
    app (Λ f) x = f x
  )
  : 1 = 0
:= False.elim (Counterexample.girard π Λ app β)
/-
The paradox assumes a formation rule `π`, incompatible with the above special case `pi` of the impredicative maximum rule. The codomain of `π` is one level below the universe of `pi`.

In the paradox, `Λ`, `app`, and `β` model $`\lambda`-abstraction, function application, and $`\beta`-reduction, respectively. These concepts are described below. The flawed formation rule `π`, together with `Λ`, `app`, and `β`, leads to the contradiction `1 = 0`.

The special case of `imax`
-/
example : Sort (imax _ 0) = Prop := rfl
/-
is related to proof irrelevance. Heuristically speaking, since proofs carry no information beyond the fact that a proposition holds, they do not enable the kind of self-referential constructions that lead to paradoxes.


# Introduction
%%%
tag := "sec-fun-introduction"
%%%

Functions are introduced by $`\lambda`-abstraction. As an illustration, we consider the [identity function][identity-function].

[identity-function]: https://en.wikipedia.org/wiki/Identity_function

-/
def I₁ {α : Sort u} : α → α := λ x ↦ x
/-
Here are some syntactic variations of the same function. {index}[`·`]
-/
def I₂ {α : Sort u} := λ x : α ↦ x

def I₃ {α : Sort u} := λ (x : α) ↦ x

def I₄ {α : Sort u} (x : α) := x

variable {α : Sort u} in
def I₅ (x : α) := x

def I₆ {α : Sort u} : α → α := (·)
/-
Observe that the codomain is not specified explicitly in these examples. Lean can infer it based on the domain.

The following function taking two arguments ignores the second one.{margin}[In the context of combinatory logic, this function is called the [combinator K][combinator-K].]

[combinator-K]: https://en.wikipedia.org/wiki/Combinatory_logic#Examples_of_combinators

-/
def K₁ {α β: Type} : α → (β → α) := λ x ↦ (λ _ ↦ x)
/-
Here are some syntactic variations of the same function.
-/
def K₂ {α β: Type} : α → β → α := λ x _ ↦ x

def K₃ {α β : Type} := λ (x : α) (_ : β) ↦ x

def K₄ {α β: Type} (x : α) (_ : β) := x

def K₅ {α β: Type} (x : α) (y : β) := x
/-


## Implicit arguments

Let us consider a variant of the identity function taking only implicit arguments.
-/
def I₁' {α : Sort u} : {_ : α} → α := λ {x} ↦ x
/-
Here are two syntactic variations of the same function.
-/
def I₂' {α : Sort u} := λ {x : α} ↦ x

def I₃' {α : Sort u} {x : α} := x
/-


# Elimination

Functions are eliminated by application.
-/
example (α β : Type) (f : α → β) (a : α) : β := f a
/-
More generally,
-/
example (I : Sort u) (X : I → Sort v)
  (f : (i : I) → X i) (i : I) :
  X i := f i
/-

[Partial application][partial-application] produces a function taking the remaining arguments.

[partial-application]: https://en.wikipedia.org/wiki/Partial_application

-/
example (α β γ: Type) (f : α → β → γ) (a : α) : β → γ := f a
/-

In contrast, _saturated application_ produces an expression that is not a function.
-/
example (α β γ: Type) (f : α → β → γ) (a : α) (b : β) :
  γ := f a b
/-


# Reduction

{ref "sec-definitional-equality-naive"}[Recall] that having the same normal form is a sufficient condition for two expressions to be definitionally equal. Computing normal forms involves several kinds of reduction. Importantly, an introduction followed immediately by the associated elimination can be reduced. In the case of functions, this is called $`\beta`-reduction.
-/
example (α : Sort u) (β : Sort v) (f : α → β) (a : α) :
  (λ x ↦ f x) a = f a
:= rfl

variable (α : Sort u) (β : Sort v) (f : α → β) (a : α) in
#reduce (λ x ↦ f x) a
/-

Although it is not strictly related to functions, we also consider another form of reduction.


## delta-reduction

$`\delta`-reduction replaces a defined name by its defining expression.{margin}[Names are referred to as constants in the Lean Language Reference, see [Definitions][definitions].]

[definitions]: https://lean-lang.org/doc/reference/latest/Definitions/Definitions/#The-Lean-Language-Reference--Definitions--Definitions

-/
def ℕ2 := ℕ × ℕ

example : ℕ2 = (ℕ × ℕ) := rfl
/-

By default, `#reduce` does not reduce inside types for performance reasons.
-/
#reduce ℕ2
/-
We can force reduction inside types as follows.
-/
#reduce (types := true) ℕ2
/-

The following example combines $`\beta`- and $`\delta`-reduction.
-/
example : I₁ 0 = 0 := rfl

#reduce I₁ 0
/-


# Equality
%%%
tag := "sec-function-eta-equivalence"
%%%

In addition to reduction, definitional equality identifies certain expressions that differ only by trivial abstraction. This identification is called $`\eta`-equivalence. For functions, $`\eta`-equivalence says that a function is definitionally equal to the $`\lambda`-abstraction obtained by applying the function to an argument.
-/
example (α : Sort u) (β : Sort v) (f : α → β)
  : (λ x ↦ f x) = f
:= rfl
/-
The definitional equality of the left and right-hand sides is not based on them having the same normal form. In fact, the left-hand side does not reduce.
-/
variable (α : Sort u) (β : Sort v) (f : α → β) in
#reduce λ x ↦ f x
/-

Reduction and $`\eta`-equivalence differ in a fundamental way: the former has an [intensional][intensional-extensional] nature while the latter is a limited kind of extensionality.

[intensional-extensional]: https://en.wikipedia.org/wiki/Extensional_and_intensional_definitions

The principle of [functional extensionality][extensionality-principles] holds in Lean, but not by `rfl`.{margin}[We give a proof of `funext` {ref "sec-function-extensionality-proof"}[later].]
-/
example (α : Sort u) (β : Sort v) (f g : α → β)
  (h : ∀ (x : α), f x = g x)
  : f = g
:= funext h
/-
[extensionality-principles]: https://en.wikipedia.org/wiki/Extensionality#Extensionality_principles


# Local definitions

Consider the following function.
-/
def pq₁ (x : ℕ) : ℕ :=
  (x + 1)^2 + 3*(x + 1) + 1
/-

We can avoid repeating the expression `x + 1` by composing two functions.
-/
def q (x : ℕ) : ℕ := x + 1
def p (y : ℕ) : ℕ := y^2 + 3*y + 1
def pq₂ (x : ℕ) := p (q x)
/-

This introduces two names `p` and `q`. Such auxiliary definitions can be avoided as follows. {index}[have]
-/
def pq₃ (x : ℕ) :=
  have y := x + 1
  y^2 + 3*y + 1
/-
Here `have` is syntactic sugar for $`\lambda`-abstraction and application.
-/
example (α : Sort u) (β : Sort v) (a : α) (b : β) :
  (
    have x : α := a
    b
  ) = (λ x : α ↦ b) a := rfl
/-
The parentheses around the `have` syntax can be omitted.
-/
example (α : Sort u) (β : Sort v) (a : α) (b : β) :
  have x : α := a
  b = (λ x : α ↦ b) a := rfl
/-

In particular, the following coincides with `pq₂`.
-/
def pq₄ (x : ℕ) :=
  (λ y ↦ y^2 + 3*y + 1) (x + 1)
/-


## Steps in proofs
%%%
tag := "sec-proof-steps"
%%%

A typical use of `have` is to isolate steps in proofs. Consider the universal instantiation followed by modus ponens.
-/
example (α : Sort u) (P Q : α → Prop)
  (h1 : ∀ a : α, P a → Q a) (h2 : ∀ a : α, P a)
  : ∀ a : α, Q a
:=
  λ a : α ↦
  have Pa := h2 a
  h1 a Pa
/-
We can read the first line of the example as introducing the symbols involved in the statement, which itself consists of the second and third lines. The statement is:

* Suppose `h1 : …` and `h2 : …`.
* Then `∀ a : α, Q a`.

The leading `:` on the third line reads as "Then" and `:=` on the fourth line as "Proof:".{margin}[It is due to this reading that we prefer the indentation in the example over the one in [Mathlib's style guidelines][style-guide]. When not proving a proposition, we adopt the usual indentation style.] The proof has the reading:

[style-guide]: https://leanprover-community.github.io/contribute/style.html#structuring-definitions-and-theorems

1. Let `a : α`.
2. We have `P a` by hypothesis `h2`, applied to `a`.
3. We conclude by hypothesis `h1`, applied to `a` and the fact `P a`.

Naming every intermediate step can become cumbersome. Omitting the name after `have` makes the step accessible as `this`.
-/
example (α : Sort u) (P Q : α → Prop)
  (h1 : ∀ a : α, P a → Q a) (h2 : ∀ a : α, P a)
  : ∀ a : α, Q a
:=
  λ a : α ↦
  have : P a := h2 a
  h1 a this
/-
A proof can also be referenced by its type using `‹…›` notation.{margin}[This introduces no ambiguity, since any two proofs of the same proposition are equal.] {index}[`‹…›`]
-/
example (α : Sort u) (P Q : α → Prop)
  (h1 : ∀ a : α, P a → Q a) (h2 : ∀ a : α, P a)
  : ∀ a : α, Q a
:=
  λ a : α ↦
  have : P a := h2 a
  h1 a ‹P a›
/-


## Syntactic abbreviation

A more general [abbreviation][local-def] is given by `let`. {index}[let]

[local-def]: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#local-definitions

-/
def pq₅ (x : ℕ) : ℕ :=
  let y := x + 1
  y^2 + 3*y + 1
/-

There are cases where `let` is applicable but `have` is not.
-/
def I₇ {α : Sort u} :=
  let t := α
  λ x : t ↦ x
/-

Syntactic abbreviation is unfolded by $`\zeta`-reduction.

{index}[`;`]
-/
example : (let t := ℕ; t × t) = (ℕ × ℕ) := rfl

#reduce (types := true) (let t := ℕ; t × t)
/-
The semicolon is a syntactic device that allows multiple expressions to be written on a single line. Replacing it by a line break leaves the expression intact.

The following example combines $`\beta`-, $`\delta`-, and $`\zeta`-reduction.
-/
example : I₇ 0 = 0 := rfl

#reduce I₇ 0
/-


# On inference of implicit arguments

Implicit arguments let us omit information that Lean can usually infer from the surrounding context. As an illustration, we return to the two syntactic variants `I₁` and `I₂` of the identity function. They both take an implicit argument, denoted by `α` in the following examples.
-/
example : {α : Sort u} → α → α := I₁

example : {α : Sort u} → α → α := I₂
/-
In the next example, the implicit argument is inferred to be `ℕ`.
-/
example : I₁ 0 = I₂ 0 := rfl
/-

The inference can stall if the surrounding context is not informative enough. While `α` appears on the left-hand side of `:` in the following example, nothing fixes it on the right-hand side, that is, in `I₁ = I₂`.
```lean +error
example (α : Sort u) : I₁ = I₂ := rfl
```
To prove the equality of `I₁` and `I₂`, we must provide more information or use the explicit versions.
-/
example (α : Sort u) : (I₁ : α → α) = I₂ := rfl

example : @I₁ = @I₂ := rfl
/-
Perhaps the cleanest way to specify implicit arguments is to use named arguments. {index}[`(… := …)`]
-/
example (α : Sort u) : I₁ (α := α) = I₂ := rfl

example (β : Sort u) : I₁ (α := β) = I₂ := rfl
/-
The left-hand side of `:=` in `(α := α)` refers to the argument `α` in the definition of `I₁` and the right-hand side to the argument of the anonymous function defined by the example. The second example renames the latter argument to make the distinction visible.

The variant of the identity function taking only implicit arguments is harder to disambiguate: fixing `α` alone is not enough.
```lean +error
example (α : Sort u) : I₁' (α := α) = I₂' := rfl
```
Nonetheless, the explicit versions of `I₁'` and `I₂'` coincide.
-/
example : @I₁' = @I₂' := rfl
/-
Unlike `I₁'`, whose second argument is anonymous, the second arguments of `I₂'` and `I₃'` are both named `x` and can be referred to as follows.
-/
example (α : Sort u) (x : α)
  : I₂' (x := x)  = I₃' (x := x) := rfl
/-
Here `α` can be inferred since it is the type of `x`.


# Rules of the type theory

The following rules govern the concepts introduced so far. They constitute a pure type system. For each rule, we first present an example and then its abstract formulation. In the abstract formulations, we write $`\operatorname{Sort}_{u}` for `Sort u`, $`\Pi x : \alpha.\; \beta` for `(x : α) → β x`, and $`\equiv` for definitional equality. Moreover, $`\Gamma` denotes an arbitrary [typing context][typing-context] and $`\beta[x := a]` denotes [substitution][substitution].{margin}[The substitution replaces all free occurrences of $`x` in the expression $`\beta` with the expression $`a`.] We use the [standard notation][typing-rule] for typing rules.

[substitution]: https://en.wikipedia.org/wiki/Lambda_calculus_definition#Substitution
[typing-context]: https://en.wikipedia.org/wiki/Typing_environment
[typing-rule]: https://en.wikipedia.org/wiki/Typing_rule

1. Axioms

-/
example : Sort (u + 1) := Sort u
/-
$$`
\frac{
}{
\vdash
\operatorname{Sort}_{u} : \operatorname{Sort}_{u + 1}
}
`

2. Start

-/
example (α : Sort u) (a : α) : α := a
/-
$$`
\frac{
\Gamma \vdash  \alpha : \operatorname{Sort}_{u}
}{
\Gamma, a : \alpha \vdash  a : \alpha
}
`

3. [Weakening][weakening]

[weakening]: https://en.wikipedia.org/wiki/Monotonicity_of_entailment

-/
example (α : Sort u) (a : α) (β : Sort v) (b : β) : α := a
/-
$$`
\frac{
\Gamma \vdash  a : \alpha
\quad
\Gamma \vdash  \beta : \operatorname{Sort}_v
}{
\Gamma, b : \beta \vdash  a : \alpha
}
`

4. Product{margin}[This is the {ref "sec-impredicative-lub-rule"}[impredicative maximum rule].]

-/
example (α : Sort u) (β : α → Sort v) :
  Sort (imax u v) := (x : α) → β x
/-
$$`
\frac{
\Gamma \vdash  \alpha : \operatorname{Sort}_{u}
\quad
\Gamma, x : \alpha \vdash  \beta : \operatorname{Sort}_{v}
}{
\Gamma \vdash  \Pi x : \alpha.\; \beta
: \operatorname{Sort}_{\operatorname{imax} u \; v}
}
`

5. Application

-/
example (α : Sort u) (β : α → Sort v)
  (f : (x : α) → β x) (a : α) :
  β a := f a
/-
$$`
\frac{
\Gamma \vdash  f : \Pi x : \alpha.\; \beta
\quad
\Gamma \vdash  a : \alpha
}{
\Gamma \vdash  f\; a : \beta[x := a]
}
`

6. Abstraction

-/
example (α : Sort u) (β : α → Sort v)
  (f : (a : α) → β a) :
  (a : α) → β a := λ x ↦ f x
/-
$$`
\frac{
\Gamma, x : \alpha \vdash  e : \beta
\quad
\Gamma \vdash  \Pi x : \alpha.\; \beta
: \operatorname{Sort}_{v}
}{
\Gamma \vdash
\lambda x : \alpha \mapsto e
: \Pi x : \alpha.\; \beta
}
`

7. Conversion

-/
example (α : Sort u) (a : α) :
  let β := α
  β := a
/-
$$`
\frac{
\Gamma \vdash  a : \alpha
\quad
\Gamma \vdash  \alpha\equiv\beta
}{
\Gamma \vdash  a : \beta
}
`


# Further proofs

-/
example : @I₁ = @I₂ := rfl
example : @I₁ = @I₃ := rfl
example : @I₁ = @I₄ := rfl
example : @I₁ = @I₅ := rfl
example : @I₁ = @I₆ := rfl
example : @I₁ = @I₇ := rfl
example : @I₁ = @I₁' := rfl

example : @K₁ = @K₂ := rfl
example : @K₁ = @K₃ := rfl
example : @K₁ = @K₄ := rfl
example : @K₁ = @K₅ := rfl

example : @I₁' = @I₂' := rfl
example : @I₁' = @I₃' := rfl

example : pq₁ = pq₂ := rfl
example : pq₁ = pq₃ := rfl
example : pq₁ = pq₄ := rfl
example : pq₁ = pq₅ := rfl
