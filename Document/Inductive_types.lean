/-
Inductive types
%%%
tag := "sec-inductive-types"
%%%
-/
import Mathlib
/-
-/
-- -show
namespace Document.Inductive_types
/-
While a pure type system can encode types of data using [Church encoding][Church_encoding], working with such encoding could feel cumbersome. [Inductive types][inductive-types] extend Lean's pure type system and provide the primary means of encoding types of data, including the natural numbers.

[inductive-types]: https://en.wikipedia.org/wiki/Inductive_type
[Church_encoding]: https://en.wikipedia.org/wiki/Church_encoding

Let us {ref "sec-intro-inductive-types"}[return] to the definition of natural numbers, reproduced here.
-/
inductive Nat' : Type where
  | zero : Nat'
  | succ (n : Nat') : Nat'
/-
The `inductive` command causes the kernel to synthesize formation, introduction, elimination, and reduction rules for a fresh inductive type. The above command defines, in particular, the two constructors `Nat'.zero` and `Nat'.succ` that determine how expressions of type `Nat'` can be introduced.

The following expressions correspond to `1` and `2`.
-/
def one := Nat'.succ Nat'.zero
def two := Nat'.succ (Nat'.succ Nat'.zero)
/-
In fact, the numerals `0`, `1`, `2`, … are syntactic sugar for expressions composed from the constructors of `Nat` in the same manner.
-/
example : 0 = Nat.zero := rfl
example : 1 = Nat.succ Nat.zero := rfl
example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl
/-


# Preliminaries

As expected, `two` is the [successor][succ] of `one`.

[succ]: https://en.wikipedia.org/wiki/Successor_function

-/
example : two = Nat'.succ one := rfl
/-
Here the left and right-hand sides of the equality have the same normal form.
-/
#reduce two
#reduce Nat'.succ one
/-
We will next explain the hierarchical name appearing in the normal form.


## Hierarchical names
%%%
tag := "sec-hierarchical-names"
%%%

Periods separate components of hierarchical names like {lean}`Nat.zero`. {index}[`.`] Lean uses this notation for several related [identifiers][identifiers]:{margin}[This list is not exhaustive.]

[identifiers]: https://lean-lang.org/doc/reference/latest/Terms/Identifiers/#identifiers-and-resolution

1. a name in a namespace,
2. a shorthand: `a.name` may stand for `α.name a` when `a : α`, or
3. a projection of a field from a structure.

In the first case, all but the final component of a hierarchical name constitute the [namespace][namespace], while the final component is the name itself. This case includes:
-/
example : Nat := Nat.zero
example : Nat → Nat := Nat.succ
/-
where the namespace is `Nat`, and the names are `zero` and `succ`, respectively. Likewise, it includes the following example from [Mathlib][mathlib] stating that any prime number is nonzero.

[mathlib]: https://mathlib.org/

-/
example (n : ℕ) : Nat.Prime n → n ≠ 0 := Nat.Prime.ne_zero
/-
Here the name is `ne_zero`, and the namespace is `Nat.Prime`.

An example of the second case is given by
-/
example : Nat'.zero.succ =  Nat'.succ Nat'.zero := rfl

#reduce one
/-

We will return to the third case {ref "sec-structures"}[below].

We can open {index}[open] the namespace of `Nat'`, and then write `zero` and `succ` instead of `Nat'.zero` and `Nat'.succ`.
-/
open Nat' in
def three := succ (succ (succ zero))

open Nat' in
example : three = zero.succ.succ.succ := rfl
/-


# Formation
%%%
tag := "sec-inductive-type-formation"
%%%

In addition to constructors, the `inductive` command specifies a type constructor for the fresh inductive type, governing its formation. Every type constructor must have a universe as its final codomain.{margin}[{ref "sec-functions-formation"}[Recall] that the final codomain was discussed in the context of function types.] For the natural numbers and Cartesian product, this is `Type` and `Type (max u v)`, respectively.
-/
example : Type := Nat

example : Type u → Type v → Type (max u v) := Prod
/-

We now focus on type constructors, and consider constructorless inductive types as examples. Here is an inductive type whose type constructor shares the type with `Prod`.
-/
inductive EmptyProd
  (α : Type u) (β : Type v) : Type (max u v)

example : Type u → Type v → Type (max u v) := EmptyProd
/-

The following example is invalid since `Nat` is not a universe.
```lean +error
inductive InvalidCodomain
  (α : Type u) (β : Type v) : Nat
```


## Parameters and indices
%%%
tag := "sec-params-and-ixs"
%%%

{ref "sec-fun-introduction"}[Recall] that the following two syntactic variations define the same identity function.
-/
def I₁ {α : Sort u} : α → α := λ x ↦ x

def I₂ {α : Sort u} (x : α) : α := x
/-
Whether an argument is written to the left or the right of `:` is merely cosmetic for a function, but for a type constructor the two sides play distinct role. Arguments on the left-hand side are _parameters_ and those on the right-hand side are _indices_. Constructors inherit the parameters as implicit arguments, but not the indices. We will {ref "sec-inductive-types-intro"}[return] to this.

`EmptyProd` has two parameters.
-/
#print EmptyProd
/-
Indices appear in `Eq` that encodes equality. Its type constructor takes three arguments, the being first implicit.
-/
example : {α : Sort u} → α → α → Prop := Eq
/-
Only the first two arguments are parameters, the third is an index. Their difference becomes clear when we consider the {ref "sec-inductive-types-intro"}[constructor] and {ref "sec-arguments-of-recursors"}[recursor] of `Eq`.
-/
#print Eq
/-
Here is a constructorless inductive type whose type constructor has the same type as `Eq`.{margin}[We disable [auto-promotion of indices][auto-promote-indices], a translation at the elaboration stage that promotes indices to parameters whenever possible.]

[auto-promote-indices]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#inductive___autoPromoteIndices

-/
set_option inductive.autoPromoteIndices false in
inductive EmptyEq {α : Sort u} (a : α) : α → Prop

#print EmptyEq
/-


## Universes
%%%
tag := "sec-universe-placement"
%%%

We can encode natural numbers in the universe right above `Type`.{margin}[We show {ref "sec-peano"}[later] that both `Nat` and `NextLevelNat` satisfy the [Peano axioms][peano].]

[peano]: https://en.wikipedia.org/wiki/Peano_axioms

-/
inductive NextLevelNat : Sort 2 where
  | zero : NextLevelNat
  | succ (n : NextLevelNat) : NextLevelNat
/-
In contrast, the following inductive type does not encode natural numbers.
-/
inductive NotNat : Sort 0 where
  | zero : NotNat
  | succ (n : NotNat) : NotNat
/-
Indeed, `NotNat` inhabits `Prop`, the universe of propositions, and
-/
example : NotNat.zero = NotNat.succ NotNat.zero := rfl
/-
due to proof irrelevance.


# Introduction
%%%
tag := "sec-inductive-types-intro"
%%%

Expressions of an inductive type are introduced using its constructors. The Cartesian product has a single constructor called `Prod.mk`.
-/
example :
  {α : Type u} → {β : Type v} → α → β → Prod α β := Prod.mk
/-
We define our version.
-/
inductive Prod' (α : Type u) (β : Type v) : Type (max u v)
  where
  | mk (fst : α) (snd : β) : Prod' α β

example :
  {α : Type u} → {β : Type v} →
  α → β → Prod' α β := Prod'.mk
/-
The parameters `α` and `β` are shared by the type constructor `Prod'` and the constructor `Prod'.mk`. The latter takes them as implicit arguments. Its remaining arguments, `fst` and `snd`, are called _fields_.

Earlier we considered the product of `ℕ` with itself and used the notation `(0, 1)`, which is syntactic sugar for `Prod.mk 0 1`.
-/
example : (0, 1) = Prod.mk 0 1 := rfl
/-

The inductive type `Sum` encodes [disjoint union][disjoint-union]. It can be defined as follows.

[disjoint-union]: https://en.wikipedia.org/wiki/Disjoint_union

-/
inductive Sum' (α : Type u) (β : Type v) : Type (max u v)
  where
  | inl (a : α) : Sum' α β
  | inr (b : β) : Sum' α β
/-
Both the constructors `Sum'.inl` and `Sum'.inr` take the parameters `α` and `β` as implicit arguments and have one field.
-/
example :
  {α : Type u} → {β : Type v} →
  α → Sum' α β := Sum'.inl

example :
  {α : Type u} → {β : Type v} →
  β → Sum' α β := Sum'.inr
/-

The inductive type `Eq` can be defined as follows.{margin}[Our `Eq'` is not quite the same as the standard `Eq`. The constructor of the latter takes the second parameter explicitly rather than implicitly. We take the view that `Eq` abuses auto-promotion of indices and that `Eq'` is a more natural way to define equality. Counterarguments to this view are [welcome][refute].]

[refute]: https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Why.20the.20constructor.20of.20Eq.20doesn't.20take.20implicit.20parameters.3F/with/577656843

-/
inductive Eq' {α : Sort u} (a : α) : α → Prop where
  | refl : Eq' a a
/-
The constructor `Eq'.refl` takes the parameters `α` and `a` as implicit arguments and has no fields.
-/
example : {α : Sort u} → {a : α} → Eq' a a := Eq'.refl
/-
Applying the constructor `Eq'.refl` to an expression `a` gives `Eq' a a`, where the parameter and index of type `α` take the same value `a`. As a result, we can construct an expression of type `Eq' a a` for any `a`, but we cannot construct expressions of type `Eq' a b` when `a` and `b` are distinct (modulo definitional equality). In this way, `Eq'` encodes the equality between expressions.


## Anonymous constructor syntax
%%%
tag := "sec-anon-const-syntax"
%%%

If an inductive type has a single constructor, then this constructor is eligible for the [anonymous constructor syntax][anon-const-syntax]: instead of writing the constructor's name applied to its arguments, the arguments can be enclosed in angle brackets and separated with commas. {index}[`⟨…⟩`]

[anon-const-syntax]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#anonymous-constructor-syntax

-/
example
  (α : Type u) (β : Type v) (a : α) (b : β)
  : Prod'.mk a b = ⟨a, b⟩
:= rfl
/-


## Well-formedness requirements
%%%
tag := "sec-well-formedness"
%%%

Constructors of the inductive type are subject to a number of [well-formedness requirements][well-formedness-req]. Consider an inductive type and write `T`, `a1, …, an`, and `c1, …, cm` for its type constructor, parameters, and constructors. {ref "sec-inductive-type-formation"}[Recall] that `T` has a universe as its final codomain. Write `Sort u` for this universe. For each `i = 1, …, m`:

[well-formedness-req]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#well-formed-inductives

* The constructor `ci` must have a saturated application of `T` as its final codomain.

* The parameters must appear uniformly in `ci`. That is, for any application `T b1 … bk`, `bj` must be definitionally equal to `aj` for `j = 1, …, n`.

* If `u > 0` then for each field `x` of `ci`, writing `α` for the type of `x`, the type `Sort v` of `α` must satisfy `v ≤ u`.{margin}[This universe level requirement is similar to the {ref "sec-impredicative-lub-rule"}[impredicative maximum rule].]

In addition, inductive types must satisfy a strict-positivity requirement related to elimination. We {ref "sec-strict-positivity"}[return] to this.

The following definition is invalid since the constructor does not inhabit the type constructor.
```lean +error
inductive InvalidInhabitant : Type where
  | mk : Nat
```

The following definition is invalid since the constructor inhabits an unsaturated application of the type constructor.
```lean +error
inductive UnsaturatedInhabitant (α : Type) : Type where
  | mk : UnsaturatedInhabitant
```

The following definition is invalid since the application `NonuniformProd β α` has the parameters in a wrong order.
```lean +error
inductive NonuniformParams (α β : Type) : Type where
  | mk : NonuniformParams β α
```

The following definition is invalid since its parameter `α` inhabits a universe with too large level.
```lean +error
inductive InvalidParamLevel (α : Type 1) : Type where
  | mk (x : α) : InvalidParamLevel α
```

The following definition is invalid since its field `x` inhabits a universe with too large level.
```lean +error
inductive InvalidFieldLevel : Type where
  | mk (x : Type) : InvalidFieldLevel
```


# Elimination
-/
-- -show
compile_inductive% Nat'
compile_inductive% Prod'
compile_inductive% Sum'
compile_inductive% Eq'
/-

Inductive types come with a disciplined way of elimination, reflecting their construction. This deconstruction is based on [pattern matching][pattern-matching] at the user-facing surface syntax level.{margin}[The use of both _application_ and _evaluation_ for function elimination is standard. Similarly, we employ both _elimination_ and _deconstruction_ in the context of inductive types.] Pattern matching is translated into applications of [recursors][recursor] at the elaboration stage.

The recursor of an inductive type is determined by the type constructor and the constructors. It has a function type and the name `rec` in the namespace of the inductive type. For example, the recursors of `Prod'` and `Nat'` are `Prod'.rec` and `Nat'.rec`.
-/
#print Prod'.rec
#print Nat'.rec
/-

[pattern-matching]: https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/
[recursor]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#recursors


## Pattern matching
%%%
tag := "sec-pattern-matching"
%%%

We will consider the surface level pattern matching via two examples, and study the kernel level recursors more systematically.

As the first example, we define the projection of a pair to its component by using pattern matching. {index}[match … with]
-/
def Prod'.fst {α : Type u} {β : Type v}
  (p : Prod' α β) : α :=
  match p with
  | mk a _ => a

example : (Prod'.mk 0 1).fst = 0 := rfl
/-
In fact, such projections are generated automatically.
-/
example : (Prod'.mk 0 1).1 = 0 := rfl
example : (Prod'.mk 0 1).2 = 1 := rfl
/-
The following shorthand is also available, reflecting the anonymous constructor syntax.
-/
example (α : Type u) (β : Type v) (pair : Prod α β) : α :=
  let ⟨a, _⟩ := pair
  a
/-

We can define the projection of a pair to its component by using the recursor of `Prod'` directly.
-/
def Prod'.fst' {α : Type u} {β : Type v}
  := @Prod'.rec α β (λ _ ↦ α) (λ a _ ↦ a)
/-
Here `λ a _ ↦ a` corresponds to the pattern `mk a _ => a`. We will return to the other arguments.

The earlier function `Prod'.fst` is translated to the same use of the recursor.
-/
example (α : Type u) (β : Type v) (p : Prod' α β) :
  Prod'.fst p = Prod'.fst' p := rfl
/-

As the second example, let us define the [predecessor][predecessor] function using pattern matching.

[predecessor]: https://en.wikipedia.org/wiki/Primitive_recursive_function#Predecessor

-/
def Nat'.pred (n : Nat') : Nat' :=
  match n with
  | zero => zero
  | succ m => m
/-
The predecessor function maps `n` constructed as `zero` to `zero`, and `n` constructed as `succ m` to `m`. We can define the same function using the recursor of `Nat'` directly.
-/
def Nat'.pred' := @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m)
/-
Here `zero` corresponds to the pattern `zero => zero` and `λ m _ ↦ m` to `succ m => m`.

The translation of `Nat'.pred` generated by Lean results in a more complicated expression than the one defining `Nat'.pred'`. We can show that these two functions are equal, but not by `rfl` alone.{margin}[After asking the pretty-printer to be verbose by setting the option `pp.all` to `true`, it is possible to start from `#print Nat'.pred` and trace how `Nat'.pred` is actually translated to an evaluation of `Nat'.rec`.]
-/
open Nat' in
example (n : Nat') : pred n = pred' n
:= rec rfl (λ _ _ ↦ rfl) n
/-


## Recursors
%%%
tag := "sec-arguments-of-recursors"
%%%

We will study the types of recursors of `Prod'`, `Sum'`, `Eq'`, and `Nat'`. Consider the type of `Prod'.rec`, labelled with comments.{margin}[In Lean, a line comment is written using `--`, {index}[`--`] while `/-` begins a block comment and `-/` ends it.] {index}[`/- … -/`]
-/
example :
  {α : Type u} → {β : Type v} /- parameters -/ →
  {motive : Prod' α β → Sort w} /- motive -/ →

  -- minor premises:
  ((a : α) → (b : β) → motive (Prod'.mk a b)) /- mk -/ →

  (p : Prod' α β) /- major premise -/ →
  motive p /- codomain -/
:= Prod'.rec
/-
All recursors take a _motive_ as an implicit argument and a _major premise_ as an explicit argument. The motive specifies the codomain depending on the major premise. For example, the codomain `α` of `Prod'.fst'` does not depend on the major premise `p`.
-/
example : {α : Type u} → {β : Type v} →
  (p : Prod' α β) → α := Prod'.fst'
/-
The motive `λ _ ↦ α` ignores its argument in the definition of `Prod'.fst'`.

If an inductive type has parameters, its recursor takes them as implicit arguments preceding the motive. For each constructor, the recursor additionally takes an explicit argument following the motive, called a _minor premise_. A minor premise takes the constructor's fields as arguments, and its final codomain is determined by the motive. It specifies how an expression introduced by that constructor is eliminated. For example, the minor premise `λ a _ ↦ a` in the definition of `Prod'.fst'` eliminates an expression of the form `Prod'.mk a b` to `a`.

The recursor of `Sum'` differs from that of `Prod'` only in minor premises: since `Sum'` has two constructors, there are two minor premises.
-/
example :
  {α : Type u} → {β : Type v} /- parameters -/ →
  {motive : Sum' α β → Sort w} /- motive -/ →

  -- minor premises:
  ((a : α) → motive (Sum'.inl a)) /- inl -/ →
  ((b : β) → motive (Sum'.inr b)) /- inr -/ →

  (p : Sum' α β) /- major premise -/ →
  motive p /- codomain -/
:= Sum'.rec
/-

The recursor of `Eq'` differs more from that of `Prod'` due to the presence of an index.
-/
example :
  {α : Sort u} → {a : α} /- parameters -/ →
  {motive : (x : α) → Eq' a x → Sort v} /- motive -/ →

  -- minor premises:
  motive a Eq'.refl /- refl -/ →

  (b : α) /- indices -/ →
  (h : Eq' a b) /- major premise -/ →
  motive b h /- codomain -/
:= Eq'.rec
/-
In general, if an inductive type has indices, its recursor takes them as explicit arguments preceding the major premise.

For `Prod'` and `Sum'`, the domain of the motive coincides with the type of major premise. For `Eq'`, the domain of the motive is the $`\Pi`-type `(x : α) → Eq' a x` whose codomain `Eq' a x` differs from the type of major premise only in the index.

The distinction between parameters and indices is apparent in recursors. Parameters are uniform in the sense that they precede all other arguments of the recursor. By contrast, indices precede only the major premise and occur as additional arguments of the motive.

The recursor of `Nat'` does not have any parameters or indices.
-/
example :
  (motive : Nat' → Sort u) /- motive -/ →

  -- minor premises:
  motive Nat'.zero /- zero -/ →
  ((m : Nat') → motive m → motive m.succ) /- succ -/ →

  (n : Nat') /- major premise -/ →
  motive n /- codomain -/
:= @Nat'.rec
/-
The constructor
-/
example : Nat' → Nat' := Nat'.succ
/-
takes a _recursive argument_, that is, an argument of the same inductive type it constructs. The second argument in the associated minor premise is an _induction hypothesis_. In general, a minor premise takes an induction hypothesis for each recursive argument. We will return to induction {ref "sec-induction"}[later].


## Strict positivity
%%%
tag := "sec-strict-positivity"
%%%

The [strict-positivity][strict-positivity] requirement rules out inductive types whose recursors would be inconsistent.{margin}[The kernel enforces this requirement by a syntactic check, rather than by detecting an inconsistency. The requirement also rules out some inductive types that would not in fact be problematic.] For instance, the following definition is invalid since it violates this requirement.

[strict-positivity]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#strict-positivity

```lean +error
inductive Bad where
  | mk : (Bad → Bad) → Bad
```

To understand why `Bad` must be rejected, consider
-/
inductive NotBad where
  | mk : (True → NotBad) → NotBad

set_option pp.proofs true in
#print NotBad.rec
/-
Extrapolating naively from the type of `NotBad.rec` by replacing `NotBad` and `True` with `Bad`, we are led to the following hypothetical recursor `rec` for `Bad`. The existence of such a recursor would yield a contradiction.
-/
example (Bad : Sort u) (mk : (Bad → Bad) → Bad)
  (rec :
    (motive : Bad → Prop) /- motive -/ →

    -- minor premise:
    (
      (f : Bad → Bad) →
      ((hi : Bad) → motive (f hi)) →
      motive (mk f)
    ) →

    (b : Bad) /- major premise -/ →
    motive b /- codomain -/
  )
  : 1 = 0
:=
  let motive := λ _ ↦ 1 = 0
  let b := mk (λ x ↦ x)
  rec motive (λ f hi ↦ hi (mk f)) b
/-


# Reduction
%%%
tag := "sec-iota-reduction"
%%%

$`\iota`-reduction governs the interaction between recursors and constructors. It reduces applications of a recursor whose major premise is a constructor by selecting the corresponding minor premise.

-/
open Nat' in
example : @rec (λ _ ↦ Nat') zero (λ m _ ↦ m) zero = zero
:= rfl

open Nat' in
#reduce @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) zero
/-
Here the major premise is `zero`, corresponding to the _first_ constructor of `Nat'`. Accordingly, $`\iota`-reduction selects the _first_ minor premise, namely `zero`.

-/
open Nat' in
example (n : Nat')
  : @rec (λ _ ↦ Nat') zero (λ m _ ↦ m) (succ n) = n
:= rfl

open Nat' in
variable (n : Nat') in
#reduce @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) (succ n)
/-
Here the major premise is `succ n`, corresponding to the _second_ constructor of `Nat'`. Accordingly, $`\iota`-reduction selects the _second_ minor premise `λ m _ ↦ m`, which is then applied to the argument `n` of the major premise `succ n`.

Together with $`\beta`- and $`\delta`-reductions, $`\iota`-reduction enables the following.
-/
open Nat' in
example : pred zero = zero := rfl

open Nat' in
example (n : Nat') : pred (succ n) = n := rfl

open Nat' in
#reduce pred zero

open Nat' in
variable (n : Nat') in
#reduce pred (succ n)
/-


# Equality

{ref "sec-function-eta-equivalence"}[Recall] that function $`\eta`-equivalence identifies a function with the $`\lambda`-abstraction obtained by applying it to an argument. There is an analogous $`\eta`-equivalence for inductive types with a single constructor and no indices.
-/
variable (x : Prod' ℕ ℕ)

example : ⟨x.1, x.2⟩ = x := rfl
/-
Written without syntactic sugar, this is
-/
example : Prod'.mk x.1 x.2 = x := rfl
/-
The definitional equality of the left and right-hand sides is not based on them having the same normal form. In fact, their normal forms differ.
-/
#reduce Prod'.mk x.1 x.2
#reduce x
/-

An inductive type can be viewed as being freely generated by its constructors: two expressions inhabiting it are equal only if they are introduced using the same constructor taking equal arguments. In other words, expressions introduced using distinct constructors are distinct, and each constructor is injective.
-/
example (n : Nat') : Nat'.succ n ≠ Nat'.zero := nofun

example (n m : Nat') (h : Nat'.succ n = Nat'.succ m) : n = m
:= Nat'.succ.inj h
/-
Lean generates injectivity theorems such as `Nat'.succ.inj` automatically. Their proofs use recursors. We will {ref "sec-equality"}[return] to constructor distinctness and injectivity.


# Structures
%%%
tag := "sec-structures"
%%%

The user-facing surface syntax `structure` {index}[structure] offers a number of conveniences. [Structures][structures] are translated to inductive types with a single constructor and no indices. The Cartesian product is a structure.

[structures]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structures

-/
#print Prod

namespace Demo

structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β

end Demo
/-
We introduced the [namespace][namespace] `Demo` to avoid a clash with the existing name `Prod`.

[namespace]: https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#namespaces

The constructor is named `mk`,{margin}[Name `mk` is used unless a name is provided with `::` {index}[`::`] [syntax][constructor-name].] and it has the fields `fst : α` and `snd : β`. Therefore, the above structure declaration yields the same constructor as our earlier definition of `Prod'`.

[constructor-name]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structure-constructors

For each field, a projection function is generated that extracts the field's value from the underlying type's constructor. This is the third use of hierarchical names that we alluded to earlier.
-/
example : (0, 1).fst = 0 := rfl
example : (0, 1).snd = 1 := rfl
/-

Projections of a structure are just syntactic sugar for deconstruction via pattern matching.
-/
example
  (α : Type u) (β : Type v) (p : Prod α β)
  : p.fst = match p with | Prod.mk fst _ => fst
:= rfl
/-

Structures also support a record-style notation.
-/
example : ℕ × ℕ where
  fst := 0
  snd := 0
/-


# Further proofs and remarks

The following examples illustrate syntactic sugar related to structures.
-/
example
  (α : Type u) (β : Type v) (p : Prod α β)
  : p.snd = match p with | Prod.mk _ snd => snd
:= rfl

example
  (α : Type u) (β : Type v) (p : Prod α β)
  : p.fst = match p with | ⟨fst, _⟩ => fst
:= rfl

example
  (α : Type u) (β : Type v) (p : Prod α β)
  : p.snd = match p with | ⟨_, snd⟩ => snd
:= rfl

example
  (α : Type u) (β : Type v) (p : Prod α β)
  : p = ⟨p.fst, p.snd⟩
:= rfl

example
  (α : Type u) (β : Type v) (a : α) (b : β)
  : Prod.mk a b = {
    snd := b
    fst := a
  }
:= rfl

example (α : Type u) (β : Type v) (pair : Prod α β) : β :=
  let ⟨_, b⟩ := pair
  b
/-

Projections have the expected types.
-/
example
  (α : Type u) (β : Type v) (p : Prod α β) :
  α := p.fst

example
  (α : Type u) (β : Type v) (p : Prod α β) :
  β := p.snd
/-

Distinct inductive types are not definitionally equal. The following example is invalid.
```lean +error
example : Nat = Nat' := rfl
```


## On auto-promotion of indices

We can define a version of `Prod` in a convoluted way, making use of the fact that `(λ t ↦ t) α` is definitionally equal to `α`.
-/
inductive Pro'' (α : Type u) (β : Type v) : Type (max u v)
  where
  | mk (fst : α) (snd : β) : Pro'' ((λ t ↦ t) α) β

#print Prod'
#print Pro''
/-

The following user-facing surface syntax relies on auto-promotion of indices.
-/
inductive Pr''' :
  (α : Type u) → (β : Type v) → Type (max u v)
  where
  | mk {α : Type u} {β : Type v}
    (fst : α) (snd : β) : Pr''' α β

#print Prod'
#print Pr'''
/-

The convoluted definition does not work with auto-promotion of indices.
```lean +error
inductive BadProd :
  (α : Type u) → (β : Type v) → Type (max u v)
  where
  | mk {α : Type u} {β : Type v}
    (fst : α) (snd : β) : BadProd ((λ t ↦ t) α) β
```
-/
