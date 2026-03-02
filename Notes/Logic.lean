/-
First-order logic
%%%
tag := "sec-logic"
%%%
-/
import Mathlib
/-
In general, to prove a proposition in Lean is to construct an expression having the proposition as its type. This can be viewed as a formulation of the [Curry–Howard correspondence][Curry-Howard]. More explicitly, the correspondence is summarized by the following encoding of concepts in [first-order logic][1st-order-logic]:

* well-formed [formula][formula]: an expression `p` of type {lean}`Prop`
* proof: an expression of type `p`
* formula is true: there is an expression of type `p`
* formula is false: there is no expression of type `p`
* truth `⊤`: an inductive type with a single constant constructor ([unit type][unit-type])
* falsehood `⊥`: an inductive type with no constructors ([empty type][empty-type])
* [negation][negation] `¬`: the function `λ p ↦ p → ⊥`
* [implication][implication] `→`: function type (as {ref "sec-implication"}[explained] already)
* [conjunction][conjunction] `∧`: an inductive type like {lean}`Prod` but in the universe `Prop` ([product type][product-type])
* [disjunction][disjunction] `∨`: an inductive type with two constructors, both taking a single argument ([sum type][sum-type])
* [universal quantification][universal-quantification]: $`Pi` type (as {ref "sec-universal-quantification"}[explained] already)
* [existential quantification][existential-quantification]: an inductive type with a predicate as a parameter ($`\Sigma` [type][dep-sum-type])

[Curry-Howard]: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
[1st-order-logic]: https://en.wikipedia.org/wiki/First-order_logic
[formula]: https://en.wikipedia.org/wiki/Well-formed_formula
[unit-type]: https://en.wikipedia.org/wiki/Unit_type
[empty-type]: https://en.wikipedia.org/wiki/Empty_type
[negation]: https://en.wikipedia.org/wiki/Negation
[implication]: https://en.wikipedia.org/wiki/Logical_implication
[conjunction]: https://en.wikipedia.org/wiki/Logical_conjunction
[product-type]: https://en.wikipedia.org/wiki/Product_type
[disjunction]: https://en.wikipedia.org/wiki/Logical_disjunction
[sum-type]: https://en.wikipedia.org/wiki/Sum_type
[universal-quantification]: https://en.wikipedia.org/wiki/Universal_quantification
[existential-quantification]: https://en.wikipedia.org/wiki/Existential_quantification
[dep-sum-type]: https://en.wikipedia.org/wiki/Dependent_type#%CE%A3_type


# Truth, falsehood and negation

Proposition {lean}`True` is defined as inductive types with a single constructor that takes no arguments.
-/
#print True
/-
We can define our own version encoding truth in the exact same manner.
-/
inductive True' : Prop where
  | intro : True'
/-

The proposition `True'` can be proven by the constructor.{margin}[{ref "sec-structures"}[Recall] the anonymous constructor syntax.]
-/
example : True' := True'.intro
example : True' := ⟨⟩
/-

The following syntactic sugar is available for the standard truth
-/
example : ⊤ = True := rfl
example : trivial = True.intro := rfl
/-
allowing
-/
example : ⊤ := trivial
/-


Proposition {lean}`False` is defined as an inductive type without constructors.
-/
#print False

inductive False' : Prop
/-
As there are no constructors, there are no expressions of type `False'`. However, it becomes meaningful via negation.
-/
#print Not

def Not' (p : Prop) := p → False'
/-
It follows from the above two definitions that
-/
example : (Not' False') = (False' → False') := rfl
/-

The identity function maps from a type to itself.
-/
example (α : Sort u) : id = λ (x : α) ↦ x := rfl

example : Not' False' := id
/-

The following syntactic sugar is provided.
-/
example : ⊥ = False := rfl
example : (λ p ↦ ¬p) = Not := rfl
/-
allowing
-/
example : ¬False := id
/-


# Principle of explosion

Both `False` and `False'` are uninhabited, that is,
there are no expressions of either types. Uninhabited propositions encode contradictions. From a contradiction, any proposition can be derived by the [principle of explosion][explosion].

{ref "sec-arguments-of-recursors"}[Recall] that `False.rec` is the recursor of {lean}`False`. This recursor encodes the principle of explosion.

[explosion]: https://en.wikipedia.org/wiki/Principle_of_explosion

-/
#print False.rec

example : False → False' := False.rec
/-

The arguments of the recursor are implicit, and Lean infers them from the context. The explicit version {lean}`@False.rec` is
-/
example :
  (motive : False → Sort u) /- motive -/ →
  (h : False) /- major premise -/ →
  motive h /- codomain -/
:= @False.rec
/-
and an explicit version of the above proof reads
-/
example : False → False' := @False.rec λ _ ↦ False'
/-
Here `@False.rec` is evaluated partially, and the only argument `λ _ ↦ False'` is the motive. The proof works, since the partially applied function has the domain `False` and since its codomain `motive h` is `False'`,
-/
example (α : Sort u) (a b : α) (h : a = b) :
  let motive := λ _ ↦ False'
  False' = motive h := rfl
/-

{ref "sec-pattern-matching"}[Recall] that pattern matching is implemented using recursors. The [nomatch expression][nomatch] is a pattern match with zero cases, and `nofun` is shorthand for a function with a body that applies `nomatch` to its arguments. {index}[nomatch] {index}[nofun]

[nomatch]: https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/#The-Lean-Language-Reference--Terms--Pattern-Matching--Other-Pattern-Matching-Operators

-/
example : False → False' := λ h ↦ nomatch h
example : False → False' := nofun
/-

Of course, the principle of explosion applies starting from `False'` as well.
-/
example : False' → False := False'.rec
example : False' → False := λ h ↦ nomatch h
example : False' → False := nofun
/-


# Lemmas and theorems

We can give a name to a proven proposition in several ways.
{index}[lemma] {index}[theorem]
-/
def explosion : False' → False := nofun
def explosion₁ (h : False') : False := nomatch h
lemma explosion₂ (h : False') : False := nomatch h
theorem explosion₃ (h : False') : False := nomatch h
/-
Despite the syntactic differences, all these define the same function.

Keywords `lemma` and `theorem` suggest reading `h` as a hypothesis and `False` as the conclusion.{margin}[{ref "sec-proof-steps"}[Recall] that `:` before the conclusion `False` can be read as "Then" and `:=` as "Proof:".]
-/
lemma explosion₄
  (h : False')
  : False
:=
  nomatch h
/-

Lemmas can be used in subsequent proofs.
-/
example : ¬False' := explosion
/-


# Propositional calculus

Compound propositions in [propositional calculus][propositional-calculus] are formed by using the logical connectives: conjunction, disjunction, implication, biconditional, and negation.

[propositional-calculus]: https://en.wikipedia.org/wiki/Propositional_calculus

We know already how negation and implication are encoded.

Conjunction, disjunction, and biconditional are inductive types.
-/
#print Or
#print And
#print Iff

variable (p q : Prop)

example : (p ∨ q) = Or p q := rfl
example : (p ∧ q) = And p q := rfl
example : (p ↔ q) = Iff p q := rfl
/-

Disjunction is defined as an inductive type with two constructors.
-/
inductive Or' (p q : Prop) : Prop where
  | inl (h : p) : Or' p q
  | inr (h : q) : Or' p q
/-

Conjunction has only one constructor `intro`.
-/
inductive And' (p q : Prop) : Prop where
  | intro (hl : p) (hr : q) : And' p q
/-

These definitions encode [disjunction][disjunction-intro] and [conjunction introductions][conjunction-intro]

[disjunction-intro]: https://en.wikipedia.org/wiki/Disjunction_introduction
[conjunction-intro]: https://en.wikipedia.org/wiki/Conjunction_introduction

-/
example (h : p) : Or' p q := Or'.inl h
example (h : q) : Or' p q := Or'.inr h

example (hl : p) (hr : q) : And' p q := And'.intro hl hr
example (hl : p) (hr : q) : And' p q := ⟨hl, hr⟩
/-

The definition of biconditional encodes [biconditional introduction][biconditional-introduction]

[biconditional-introduction]: https://en.wikipedia.org/wiki/Biconditional_introduction

-/
inductive Iff' (p q : Prop) : Prop where
  | intro (hmp : p → q) (hmpr : q → p) : Iff' p q

example (hl : p → q) (hr : q → p) : Iff' p q := ⟨hl, hr⟩
/-

Destructuring via pattern matching enables proofs of statements involving compound hypotheses. Below, we illustrate the [conjunction][conjunction-elim] and [biconditional elimination][biconditional-elim]

[conjunction-elim]: https://en.wikipedia.org/wiki/Conjunction_elimination
[biconditional-elim]: https://en.wikipedia.org/wiki/Biconditional_elimination

-/
example (hh : And' p q) : p
:=
  match hh with
  | ⟨h, _⟩ => h

example (hh : Iff' p q) : q → p
:=
  match hh with
  | ⟨_, h⟩ => h
/-
These are the projection functions associated to `And'` and `Iff'`. The standard `And` is a structure with fields `left` and `right` and `Iff` is a structure with fields `mp` and `mpr`.
-/
example (h : p ∧ q) : p := h.left

example (h : p ↔ q) : q → p := h.mpr
/-

Let us now turn to disjunction and consider its [commutativity][commutativity]

[commutativity]: https://en.wikipedia.org/wiki/Commutative_property#Truth_functional_connectives

Destructuring a disjunctive hypothesis results in two cases.
-/
example (h : Or' p q) : Or' q p
:=
  match h with
  | Or'.inl hp => Or'.inr hp
  | Or'.inr hq => Or'.inl hq
/-
This is a [proof by case analysis][proof-by-case-analysis]. There are two cases: `h` was either constructed with `inl` or with `inr`. In the former case, we construct a new `Or'` expression using `inr`, and in the latter case `inr` is used. In other words, we swap the roles of `inl` and `inr`.

[proof-by-case-analysis]: https://en.wikipedia.org/wiki/Proof_by_exhaustion


# Existential quantification

Existential quantification is defined as an inductive type.
-/
#print Exists

example (α : Sort u) (P : α → Prop) :
  (∃ a : α, P a) = Exists (λ x : α ↦ P x) := rfl

inductive Exists' {α : Sort u} (P : α → Prop) : Prop where
  | intro (a : α) (h : P a) : Exists' P
/-

The definition is based on [existential generalization][existential-generalization]

[existential-generalization]: https://en.wikipedia.org/wiki/Existential_generalization

-/
example (α : Sort u) (P : α → Prop) (a : α) (h : P a) :
  Exists (λ x ↦ P x) := Exists.intro a h
/-

Destructuring via pattern matching enables [existential instantiation][existential-instantiation]

[existential-instantiation]: https://en.wikipedia.org/wiki/Existential_instantiation

-/
example (α : Sort u) (P : α → Prop)
  (h1 : Exists (λ x ↦ P x)) (h2 : ∀ a : α, P a → q) : q
:=
  match h1 with
  | Exists.intro a ha => h2 a ha
/-


# Further proofs

-/
example : explosion = explosion₁ := rfl
example : explosion = explosion₂ := rfl
example : explosion = explosion₃ := rfl
example : explosion = explosion₄ := rfl
