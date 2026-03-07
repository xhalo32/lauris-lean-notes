/-
Inductive types
%%%
tag := "sec-inductive-types"
%%%
-/
import Mathlib
/-
[Inductive types][inductive-types] are the primary way to define new types in Lean. The type encoding natural numbers,  {lean}`Nat`, is an example of an inductive type. The `#print` {index}[#print] command can be used to inspect the definition of {lean}`Nat`.

[inductive-types]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/

-/
#print Nat
/-
The output shows the _type constructor_ and _constructors_ together with their types: the former is {lean}`Nat` inhabiting {lean}`Type`, while the latter are

* {lean}`Nat.zero` inhabiting `ℕ`, and{margin}[Recall that `ℕ` is syntactic sugar for {lean}`Nat`.]
* {lean}`Nat.succ` inhabiting `ℕ → ℕ`.

The constructors define how the expressions of type {lean}`Nat` arise, while the type constructor specifies that
-/
example : Type := Nat
/-

{lean}`Nat.succ` encodes the [successor function][succ]. The numerals `0`, `1`, `2`, … are syntactic sugar for expressions composed from the constructors of {lean}`Nat`.

[succ]: https://en.wikipedia.org/wiki/Successor_function
-/
example : 0 = Nat.zero := rfl
example : 1 = Nat.succ Nat.zero := rfl
example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl
/-
The only way to obtain an expression of type {lean}`Nat` is by using {lean}`Nat.succ` and {lean}`Nat.zero`.

We can define an inductive type in the same way as {lean}`Nat`. {index}[inductive … where]
-/
inductive Nat' : Type where
  | zero : Nat'
  | succ : Nat' → Nat'

#print Nat'
/-

The following expressions correspond to 1 and 2.
-/
def one := Nat'.succ Nat'.zero
def two := Nat'.succ (Nat'.succ Nat'.zero)
/-
Moreover,
-/
example : two = Nat'.succ one := rfl
/-
Here the left and right-hand sides of the equality have the same normal form:
-/
#reduce two
#reduce Nat'.succ one
/-
We will explain {ref "sec-hierarchical-names"}[below] the hierarchical name appearing in the normal form.


# Universes
%%%
tag := "sec-universe-placement"
%%%

The universe of an inductive type is specifed by its type constructor.
-/
inductive NextLevelNat : Sort 2 where
  | zero : NextLevelNat
  | succ : NextLevelNat → NextLevelNat
/-
From the mathematical point of view, `NextLevelNat` is [isomorphic][isomorphism] to {lean}`Nat`, since they both satisfy the second order [Peano axioms][peano]. We will show this {ref "sec-peano"}[later].

The following is not isomorphic to {lean}`Nat`.

[isomorphism]: https://en.wikipedia.org/wiki/Isomorphism
[peano]: https://en.wikipedia.org/wiki/Peano_axioms

-/
inductive NotNat : Sort 0 where
  | zero : NotNat
  | succ : NotNat → NotNat
/-
Indeed, `NotNat` inhabits `Sort u`, the universe of propositions, and
-/
example : NotNat.zero = NotNat.succ NotNat.zero := rfl
/-
due to proof irrelevance.

If the universe of an inductive type is not specified explicitly, Lean infers the smallest universe level compatible with the constructors.{margin}[Lean also attempts to infer the type of a constructor if it is omitted.]
-/
namespace Demo

inductive Nat where
  | zero
  | succ : Nat → Nat

end Demo
/-
We introduced the [namespace][namespace] `Demo` to avoid a clash with the existing name {lean}`Nat`.

[namespace]: https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#namespaces


# Hierarchical names
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
where the namespace is `Nat`, and the names are `zero` and `succ`, respectively; as well as:
-/
example : Nat' := Nat'.zero
example : Demo.Nat := Demo.Nat.zero
/-
where the name is `zero`, and the namespaces are `Nat'` and `Demo.Nat`, respectively.

An example of the second case is given by
-/
example : Nat'.zero.succ =  Nat'.succ Nat'.zero := rfl

#reduce one
/-

We will return to the third case {ref "sec-structures"}[below].

We can open {index}[open] the namespace of `Nat'`, and then write `zero` and `succ` instead of `Nat'.zero` and `Nat'.succ`.
-/
open Nat'

def three := succ (succ (succ zero))

example : three = zero.succ.succ.succ := rfl
/-


# Parameters and fields
%%%
tag := "sec-params"
%%%

Recall that `Prod` encodes Cartesian product. It is an inductive type with parameters. We can define our version as follows.
-/
inductive Prod' (α : Type u) (β : Type v) : Type (max u v)
  where
  | mk : (fst : α) → (snd : β) → Prod' α β
/-
The type constructor {lean}`Prod` is a function taking two arguments.
-/
example : Type u → Type v → Type (max u v) := Prod
/-
The only constructor {lean}`Prod.mk` has the type
-/
example :
  (α : Type u) → (β : Type v) →
  (fst : α) → (snd : β) → Prod α β := @Prod.mk
/-
The arguments `α` and `β` are called _parameters_. They are shared by the type constructor `Prod` and the constructor `Prod.mk`. The latter takes them as implicit arguments. Its remaining arguments, `fst` and `snd`, are called _fields_.

Earlier we considered the product of `ℕ` with itself and used the notation `(0, 1)`, which is syntactic sugar for `Prod.mk 0 1`.
-/
example : (0, 1) = Prod.mk 0 1 := rfl
/-

The inductive type `Sum` encodes [disjoint union][disjoint-union]. It can be defined as follows.

[disjoint-union]: https://en.wikipedia.org/wiki/Disjoint_union

-/
inductive Sum' (α : Type u) (β : Type v) : Type (max u v)
  where
  | inl (x : α) : Sum' α β
  | inr (x : β) : Sum' α β
/-
Both the constructors `inl` and `inr` take the parameters `α` and `β` as implicit arguments.
-/
example :
  (α : Type u) → (β : Type v) →
  (x : α) → Sum α β := @Sum.inl

example :
  (α : Type u) → (β : Type v) →
  (x : β) → Sum α β := @Sum.inr
/-

The parameters `(a1 : α1), …, (an: αn)` of the type constructor `T` of an inductive type are subject to the following _uniformity requirement_: for any application `T b1 … bm` of `T` in the definition of the type it holds that `bj` is definitionally equal to `aj` for `j = 1, …, n`.

The following definition is invalid.
```lean +error
inductive BadSum (α : Type u) (β : Type v) : Type (max u v)
  where
  | inl (x : α) : BadSum α β
  | inr (x : β) : BadSum β α
```

We can define a version of `Prod` in a convoluted way.
-/
inductive Pro'' (α : Type u) (β : Type v) : Type (max u v)
  where
  | mk : (fst : α) → (snd : β) → Pro'' ((λ t ↦ t) α) β

#print Prod'
#print Pro''
/-

The following syntax is also supported.
-/
inductive Pr''' :
  (α : Type u) → (β : Type v) → Type (max u v)
  where
  | mk : {α : Type u} → {β : Type v} →
    (fst : α) → (snd : β) → Pr''' α β

#print Prod'
#print Pr'''
/-
This syntax relies on a feature called [auto-promotion of indices][auto-promote-indices], and should be viewed as less fundamental than that in the definition of `Prod'`.

[auto-promote-indices]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#inductive___autoPromoteIndices

The convoluted definition does not work with auto-promotion of indices.
```lean +error
inductive BadProd :
  (α : Type u) → (β : Type v) → Type (max u v)
  where
  | mk : {α : Type u} → {β : Type v} →
    (fst : α) → (snd : β) → BadProd ((λ t ↦ t) α) β
```


# Indices
%%%
tag := "sec-indexed-families"
%%%

The type constructor of an inductive types can take arguments that are not shared with the constructors of the type. Such arguments are called _indices_. Indices can be seen as defining a family of types: each choice of indices selects a particular member of the family.

An example is given by {lean}`Eq` that encodes equality. We define our version as follows.{margin}[Our `Eq'` is not quite the same as the standard `Eq`. The constructor of the latter takes the second parameter explicitly rather than implicitly. We take the view that `Eq` abuses auto-promotion of indices and that `Eq'` is a more natural way to define equality. Counterarguments to this view are [welcome][refute]. {ref "sec-surface-syntax"}[Recall] also that implicit and explicit arguments do not differ at the level of the type theory.]

[refute]: https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Why.20the.20constructor.20of.20Eq.20doesn't.20take.20implicit.20parameters.3F/with/577656843

-/
#print Eq

inductive Eq' {α : Sort u} (a : α) : α → Prop where
  | refl : Eq' a a

#print Eq'
/-

The type constructor {lean}`@Eq` is a function taking three arguments.
-/
example : (α : Sort u) → (a : α) → α → Prop := @Eq
/-
The first two arguments are parameters, while the third argument is an index.

The constructor {lean}`@Eq.refl` has the type
-/
example : (α : Sort u) → (a : α) → Eq a a := @Eq.refl
/-
It has no fields.

Applying the constructor {lean}`Eq.refl` to an expression `a` gives `Eq a a`, where the parameter and index of type `α` take the same value `a`. As a result, we can construct an expression of type `Eq a a` for any `a`, but we cannot construct expressions of type `Eq a b` when `a` and `b` are distinct (modulo definitional equality). In this way, `Eq` encodes the equality between expressions.


# Recursors

Inductive types come with a disciplined way of elimination, reflecting their construction. At the user-facing surface syntax level, this elimination, or deconstruction,{margin}[The use of both _application_ and _evaluation_ for function elimination is standard. Similarly, we employ both _deconstruction_ and _elimination_ in the context of inductive types.] is done using [pattern matching][pattern-matching]. At the level of the underlying type theory, pattern matching is translated into applications of the [recursor][recursor] associated to the inductive type. The recursor is completely determined by the type constructor and the constructors.

[pattern-matching]: https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/
[recursor]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#recursors

Consider the [predecessor][predecessor] function as an example. {index}[match … with]

[predecessor]: https://en.wikipedia.org/wiki/Primitive_recursive_function#Predecessor

-/
def pred (n : Nat') : Nat' :=
  match n with
  | zero   => zero
  | succ m => m
/-
The predecessor function maps `n` constructed as `zero` to `zero`, and `n` constructed as `succ m` to `m`.


## Pattern matching via recursors
%%%
tag := "sec-pattern-matching"
%%%

The recursor of `Nat'` is `Nat'.rec`. Like all recursors, it has a function type.
-/
#print Nat'.rec
/-

To get a glimpse of how `pred` is translated into an application of `Nat'.rec`, we consider a function that is extensionally equal to `pred` and that uses `Nat'.rec` directly.{margin}[After asking the pretty-printer to be verbose by setting the option `pp.all` to `true` with `set_option` command, it is possible to start from `#print pred` and trace how `pred` is actually translated to an evaluation of `Nat'.rec`. The translation generated by Lean results in a more complicated expression than the one in our example, and these two expressions are not definitionally equal. This is why we prove equality using function extensionality rather than `rfl`.]
-/
example : pred = @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m)
:= by
  funext n
  cases n <;> rfl
/-
The first argument of `@Nat'.rec` is called the _motive_. The motive specifies the codomain of the resulting function; since this codomain may depend on the argument of the function, the motive itself is a function. In the case of `pred`, the codomain `Nat'` does not depend on the argument, and the argument of the motive is ignored.

The second argument `zero` of `@Nat'.rec` prescribes how `zero` is mapped. It corresponds to `zero => zero` in the definition of `pred`. The third argument `λ m _ ↦ m` prescribes how `succ m` is mapped and corresponds to `succ m => m`.

The constructor
-/
example : Nat' → Nat' := Nat'.succ
/-
takes a _recursive argument_, that is, an argument of the same inductive type it constructs. The ignored argument in `λ m _ ↦ m` is the _induction hypothesis_ associated to this recursive argument. While ignored here, induction hypotheses will be useful {ref "sec-induction"}[later]: as their name indicates, recursors are not used only for pattern matching.


## Arguments of recursors
%%%
tag := "sec-arguments-of-recursors"
%%%

Consider the type of {lean}`@Nat.rec`.{margin}[In Lean, a line comment is written using `--`, {index}[`--`] while `/-` begins a block comment and `-/` ends it. {index}[`/- … -/`] Here they are used to label parts of the type.]
-/
example :
  (motive : Nat → Sort u) /- motive -/ →

  -- minor premises:
  motive Nat.zero /- zero -/ →
  ((m : Nat) → motive m → motive m.succ) /- succ -/ →

  (n : Nat) /- major premise -/ →
  motive n /- codomain -/
:= @Nat.rec
/-
As above, the first argument of {lean}`@Nat.rec` is the motive. The last argument is called the _major premise_. In the case of {lean}`@Nat.rec`, the remaining arguments are called the _minor premises_.

There is one minor premise for each constructor. The type or codomain of each minor premise is determined by the motive. A minor premise takes arguments of the same type as the constructor, excluding the parameters of the type. If the constructor takes recursive arguments, the minor premise additionally takes one induction hypothesis for each such argument. In the example above, the only induction hypothesis is the argument with type `motive m` in the minor premise associated to {lean}`Nat.succ`.

Next, consider the type of {lean}`@Prod.rec`.
-/
example :
  (α : Type u) → (β : Type v) /- parameters -/ →
  (motive : α × β → Sort w) /- motive -/ →

  -- minor premises:
  ((fst : α) → (snd : β) → motive (fst, snd)) /- mk -/ →

  (pair : α × β) /- major premise -/ →
  motive pair /- codomain -/
:= @Prod.rec
/-
{lean}`Prod` is an inductive type with parameters. Its parameters precede the motive. As {lean}`Prod` has a single constructor {lean}`Prod.mk`, there is a single minor premise.

Like {lean}`Nat.succ`, {lean}`Prod.mk` is a function, but unlike {lean}`Nat.succ`, it is not recursive as it does not take an argument of type {lean}`Prod`. Hence the minor premise does not take any induction hypotheses.

Apart from the parameters `α : Type u` and `β : Type v`, the minor premise takes the same arguments as the constructor {lean}`@Prod.mk`:
-/
example :
  (α : Type u) → (β : Type v) →
  (fst : α) → (snd : β) → Prod α β := @Prod.mk
/-

Finally, consider the type of {lean}`@Eq.rec`.
-/
example :
  (α : Sort u) → (a : α) /- parameters -/ →
  (motive : (x : α) → a = x → Sort v) /- motive -/ →

  -- minor premises:
  motive a (Eq.refl a) /- refl -/ →

  (b : α) /- indices -/ →
  (h : a = b) /- major premise -/ →
  motive b h /- codomain -/
:= @Eq.rec
/-
Like for {lean}`Prod`, the parameters of {lean}`Eq` precede the motive. As {lean}`Eq` has a single constructor {lean}`Eq.refl`, there is a single minor premise. Unlike {lean}`Nat` and {lean}`Prod`, {lean}`Eq` is an indexed family of types. Its index precedes the major premise.

For {lean}`Nat` and {lean}`Prod`, the domain of the motive coincides with the type of major premise. For {lean}`Eq`, the domain of the motive is a Π-type
-/
example (α : Sort u) (a : α) :
  ((x : α) → a = x) = ((x : α) → Eq a x)
:= rfl
/-
The index `x : α` of the Π-type is of the same type as the index of {lean}`Eq`. The codomain of the Π-type differs from the type of major premise only in the index.

The distinction between parameters and indices is apparent in recursors. Parameters are uniform in the sense that they precede all other arguments of the recursor. By contrast, indices precede only the major premise and occur as additional arguments of the motive.


# Reduction of iota kind
%%%
tag := "sec-iota-reduction"
%%%

Reduction of $`\iota` kind governs the interaction between recursors and constructors. It reduces applications of a recursor whose major premise is a constructor by selecting the corresponding minor premise.

-/
example :
  @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) zero = zero
:= rfl

#reduce @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) zero
#reduce zero
/-
Here the major premise is `zero`, corresponding to the _first_ constructor of `Nat'`. Accordingly, $`\iota`-reduction selects the _first_ minor premise, namely `zero`.

-/
variable (n : Nat')

example :
  @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) (succ n) = n
:= rfl

#reduce @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) (succ n)
#reduce n
/-
Here the major premise is `succ n`, corresponding to the _second_ constructor of `Nat'`. Accordingly, $`\iota`-reduction selects the _second_ minor premise `λ m _ ↦ m`, which is then applied to the argument `n` of the major premise `succ n`.

Together with $`\beta`- and $`\delta`-reductions, $`\iota`-reduction enables the following.
-/
example : pred zero = zero := rfl
example : pred (succ n) = n := rfl

#reduce pred zero
#reduce pred (succ n)
/-


# Well-formedness requirements
%%%
tag := "sec-well-formedness"
%%%


[well-formedness-req]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#well-formed-inductives

Inductive type definintions are subject to a number of [well-formedness requirements][well-formedness-req]. The _basic shape requirements_ are:

* The type or codomain of the type constructor is a universe.
* The type or codomain of each constructor is a saturated application of the type constructor.

The _universe level requirements_ are similar to the {ref "sec-impredicative-lub-rule"}[impredicative maximum rule]. Namely, if a type inhabits `Sort u` with `u > 0`, then it is required that:

* For each parameter: if the parameter inhabits `Sort v`, then `v ≤ u`.
* For each field of each constructor: if the field inhabits `Sort v`, then `v < u`.

The following two definitions are invalid due to some of their parameters having a too large universe level.

```lean +error
inductive BadProd :
  Type (u + 1) → Type v → Type (max u v)
  where
  | mk : {α : Type (u + 1)} → {β : Type v} →
    (fst : α) → (snd : β) → BadProd α β
```

```lean +error
inductive BadProd' :
  Type u → Type (v + 1) → Type (max u v)
  where
  | mk : {α : Type u} → {β : Type (v + 1)} →
    (fst : α) → (snd : β) → BadProd' α β
```

The following definition is invalid due to the only field of its only constructor having a too large universe level.

```lean +error
inductive BadWrap : Type u where
  | mk (α : Type u) : BadWrap
```
Raising the universe level of the inductive type makes the definition valid.
-/
inductive GoodWrap : Type (u + 1) where
  | mk (α : Type u) : GoodWrap
/-

There are other requirements as well, the most important of which is [strict-positivity][strict-positivity]. For example, the following definition is invalid since it violates this requirement.

[strict-positivity]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#strict-positivity

```lean +error
inductive Bad where
  | mk : (Bad → Bad) → Bad
```


# Structures
%%%
tag := "sec-structures"
%%%


At the level of type theory, [structures][structures] are inductive types that have a single constructor and no indices. At the surface syntax level, keyword `structure` {index}[structure] offers a number of conveniences.

[structures]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structures

The Cartesian product is, in fact, a structure.
-/
#print Prod

namespace Demo'

structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β

end Demo'
/-

The constructor is named `mk`,{margin}[Name `mk` is used unless a name is provided with `::` [syntax][constructor-name].] and it has the fields `fst : α` and `snd : β`. Therefore, the above structure declaration yields the same constructor as our earlier definition of `Prod`.

[constructor-name]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#structure-constructors

For each field, a projection function is generated that extracts the field's value from the underlying type's constructor. This is the third use of hierarchical names that we alluded to earlier.
-/
example : (0, 1).fst = 0 := rfl
example : (0, 1).snd = 1 := rfl
/-

Projections of a structure are just syntactic sugar for deconstruction via pattern matching.{margin}[We will refer to all such functions as projections, provided they are associated with an inductive type that could have been defined as a structure, regardless of whether the surface-syntax keyword `structure` was actually used in its definition.]
-/
example
  (α : Type u) (β : Type v) (p : Prod α β)
  : p.fst = match p with | Prod.mk fst _ => fst
:= rfl
/-


The fields of a structure can be accessed by indices.
-/
example
  (α : Type u) (β : Type v) (p : Prod α β)
  : p.fst = p.1
:= rfl
/-

Structures also support a record-style notation.
-/
example
  (α : Type u) (β : Type v) (a : α) (b : β) :
  Prod α β := {
    fst := a
    snd := b
  }
/-


## Anonymous constructor syntax
%%%
tag := "sec-anon-const-syntax"
%%%

If an inductive type has a single constructor, then this constructor is eligible for the [anonymous constructor syntax][anon-const-syntax] `⟨…⟩`. {index}[`⟨…⟩`] This syntax can be used, in particular, with structures.

[anon-const-syntax]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#anonymous-constructor-syntax

-/
example
  (α : Type u) (β : Type v) (a : α) (b : β)
  : Prod.mk a b = ⟨a, b⟩
:= rfl
/-


# Structure eta-equivalence
%%%
tag := "sec-structure-eta-equivalence"
%%%

{ref "sec-function-eta-equivalence"}[Recall] that function $`\eta`-equivalence identifies a function with the $`\lambda`-abstraction obtained by applying it to an argument.

There is an analogous $`\eta`-equivalence for structures. If the type of an expression `x` is a structure with two fields, then `x` is definitionally equal to the expression obtained by reconstructing it from its projections, namely `⟨x.1, x.2⟩`.

More generally, structure $`\eta`-equivalence applies to structures with any number of fields. It also applies to any inductive type that could be defined as a structure, regardless of whether the surface-syntax keyword `structure` was used in its definition.

-/
variable (x : Prod' ℕ ℕ)

example : ⟨x.1, x.2⟩ = x := rfl
/-

Written without syntactic sugar, this is
-/
example : Prod'.mk x.1 x.2 = x := rfl
/-
The definitional equality of the left and right-hand sides is not based on them having the same normal form. In fact, their normal forms differ, as can be observed using `#reduce`.
-/
#reduce Prod'.mk x.1 x.2
#reduce x
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
-/
