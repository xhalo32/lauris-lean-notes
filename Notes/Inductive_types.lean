/-
Inductive types
-/
import Mathlib
/-
%%%
tag := "sec-inductive-types"
%%%


[Inductive types][inductive-types] are the primary way to define new types in Lean. The type encoding natural numbers,  {lean}`Nat`, is an example of an inductive type. Let's use the `#print` {index}[#print] command to inspect the definition of {lean}`Nat`.

[inductive-types]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/

-/
#print Nat
/-
The output shows the _type constructor_ and _constructors_ together with their types: the former is `Nat`, with type `Type`, while the latter are

* `Nat.zero`, with type `ℕ`,{margin}[Recall that ℕ is syntactic sugar for {lean}`Nat`.] and
* `Nat.succ`, with type `ℕ → ℕ`.

The constructors define how the expressions of type `Nat` arise, while the type of the type constructor places `Nat` in the universe `Sort 1`.
-/
example : Sort 1 := Nat
example : Sort 1 = Type := rfl
/-

`Nat.succ` corresponds to the [successor function][succ].

[succ]: https://en.wikipedia.org/wiki/Successor_function

The numerals 0, 1, 2, ... are syntactic sugar for expressions composed from the constructors of `Nat`.
-/
example : 0 = Nat.zero := rfl
example : 1 = Nat.succ Nat.zero := rfl
example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl
/-
The only way to obtain an expression of type `Nat` is by using `Nat.succ` and `Nat.zero`.

We can define an inductive type in the same way as `Nat`.
{index}[inductive ... where]
-/
inductive Nat' : Type where
  | zero : Nat'
  | succ : Nat' → Nat'

#print Nat'
/-

Let's also define variants of 1 and 2.
-/
def one := Nat'.succ Nat'.zero
def two := Nat'.succ (Nat'.succ Nat'.zero)
/-
Then
-/
example : two = Nat'.succ one := rfl
/-
Here the left and right-hand sides of the equality have the same normal form:
-/
#reduce two
#reduce Nat'.succ one
/-
We will explain {ref "sec-hierarchical-names"}[below] the hierarchical name appearing in the normal form.


# Placement in the universe hierarchy

The placement in the universe hierarchy can be specified with the type of type constructor.
-/
inductive NextLevelNat : Sort 2 where
  | zero : NextLevelNat
  | succ : NextLevelNat → NextLevelNat
/-
From the mathematical point of view, `NextLevelNat` is [isomorphic][isomorphism] to `Nat`, since they both satisfy the [Peano axioms][peano]. We will show this later. However, the following is not.

[isomorphism]: https://en.wikipedia.org/wiki/Isomorphism
[peano]: https://en.wikipedia.org/wiki/Peano_axioms

-/
inductive NotNat : Sort 0 where
  | zero : NotNat
  | succ : NotNat → NotNat
/-
Indeed, `NotNat` is placed in the universe of propositions, and
-/
example : NotNat.zero = NotNat.succ NotNat.zero := rfl
/-
due to proof irrelevance.

If the type of a type constructor is omitted, Lean attempts to infer a placement on the minimal level of the universe hierarchy. (Lean also attempts to infer the type of a constructor if it is omitted.)
-/
namespace Demo

inductive Nat where
  | zero
  | succ : Nat → Nat

end Demo
/-
We introduced the [namespace][namespace] `Demo` to avoid a clash with the existing name `Nat`.

[namespace]: https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#namespaces


# Hierarchical names
%%%
tag := "sec-hierarchical-names"
%%%

Periods separate components of hierarchical names like `Nat.zero`. {index}[.] Lean uses this notation for several related [identifiers][identifiers]:{margin}[This list is not exhaustive.]

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


# Type constructors with arguments

The encoding of Cartesian product is an example of an inductive type with parameters. It can be defined as follows.
-/
universe u v
namespace Demo

inductive Prod : Type u → Type v → Type (max u v) where
  | mk : {α : Type u} → {β : Type v} →
    (fst : α) → (snd : β) → Prod α β

end Demo
/-

We view the type constructor `Prod` as a function taking two arguments and having the codomain `Type (max u v)`.
-/
example : Type u → Type v → Type (max u v) := Prod
/-
The only constructor `Prod.mk` has the type
-/
example :
  (α : Type u) → (β : Type v) →
  (fst : α) → (snd : β) → Prod α β := @Prod.mk
/-
In terms of the types of their arguments, `Prod` and `@Prod.mk` have the common prefix `Type u → Type v`. We can even write
-/
example :
  (α : Type u) → (β : Type v) →
  Type (max u v) := Prod
/-
The _parameters_ of an inductive type consist of the largest prefix of arguments shared by the type constructor and all the constructors. The remaining arguments of the type constructor are called _indices_, and the remaining arguments of a constructor are called _fields_. `Prod` has the parameters `Type u` and `Type v`, but no indices. The fields of `Prod.mk` are `fst : α` and `snd : β`.

Earlier we considered the product of ℕ with itself and used the notation `(0, 1)`, which is syntactic sugar for `Prod.mk 0 1`.
-/
example : (0, 1) = Prod.mk 0 1 := rfl
/-

The following syntax is also provided.{margin}[This can not quite be called syntactic sugar, see [promotion of indices][auto-promote-indices] to parameters.]

[auto-promote-indices]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#inductive___autoPromoteIndices

-/
inductive Prod'
  (α : Type u) (β : Type v) : Type (max u v)
  where
  | mk (fst : α) (snd : β) : Prod' α β
/-


# Indexed families of types

Indices can be seen as defining a family of types: each choice of indices selects a particular member of the family.
An example is given by `Eq`,{margin}[{ref "sec-definitional-equality-naive"}[Recall] that `a = a` is syntactic sugar for `Eq a a`.] which can be defined as follows.
-/
#print Eq

namespace Demo

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl : {α : Sort u} → (a : α) → Eq a a

end Demo
/-
We view `@Eq` as a function taking three arguments and having the codomain `Prop`.
-/
example : (α : Sort u) → (a : α) → α → Prop := @Eq
/-
The only constructor `@Eq.refl` has the type
-/
example : (α : Sort u) → (a : α) → Eq a a := @Eq.refl
/-
The common prefix is `(α : Sort u) → (a : α)`. Hence, `α` and `a` are parameters, while the third argument of `@Eq` is an index. The constructor `@Eq.refl` has no fields.

The evaluation of the constructor `Eq.refl` at an expression `a` gives `Eq a a`, where the parameter and index of type `α` take the same value `a`. As a result, we can construct terms of type `Eq a a` for any expression `a`, but we cannot construct terms of type `Eq a b` when `a` and `b` are distinct (modulo definitional equality). In this way, `Eq` encodes the equality between expressions.


# Well-formedness requirements
%%%
tag := "sec-well-formedness"
%%%


[well-formedness-req]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#well-formed-inductives

Inductive type declarations are subject to a number of [well-formedness requirements][well-formedness-req]. The _basic shape requirements_ are:

* Either the type or codomain of a type constructor must be a universe. The type is said to inhabit this universe.
* For each constructor: either its type or codomain must be a saturated application of the type constructor.

The _universe level requirements_ are similar to the {ref "sec-impredicative-lub-rule"}[impredicative least upper bound rule]. Namely, if a type inhabits `Sort u` with `u > 0`, then it is required that:

* For each parameter: if the parameter is itself a type that inhabits `Sort v`, then `v ≤ u`.
* For each field of each constructor: if the field is itself a type that inhabits `Sort v`, then `v < u`.

The following two definitions are invalid due to one of their parameters having a too large universe level.

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

Placement on the next level of the universe hierarchy is valid, though.
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


# Recursors

Inductive types come with a disciplined way of deconstruction, reflecting their construction. At the user-facing surface syntax level, this deconstruction is done using [pattern matching][pattern-matching]. At the level of the underlying type theory, pattern matching is translated into applications of the [recursor][recursor] associated to the inductive type. The recursor is completely determined by the type constructor and the constructors.

[pattern-matching]: https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/
[recursor]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#recursors

Let us consider the [predecessor][predecessor] function as an example. {index}[match ... with]

[predecessor]: https://en.wikipedia.org/wiki/Primitive_recursive_function#Predecessor

-/
def pred (n : Nat') : Nat' :=
  match n with
  | zero   => zero
  | succ m => m
/-
The predecessor function maps `n` constructed as `zero` to `zero`, and `n` constructed as `succ m` to `m`.


## Pattern matching via recursors

The recursor of `Nat'` is `Nat'.rec`. It has a function type.
-/
#print Nat'.rec
/-

To get a glimpse of how `pred` is translated into an application of `Nat'.rec`, let us consider a function that is extensionally equal to `pred` and that uses `Nat'.rec` directly.{margin}[After asking the pretty-printer to be verbose with `set_option pp.all true`, it is possible to start from `#print pred` and trace how `pred` is actually translated to an evaluation of `Nat'.rec`. The translation generated by Lean results in a more complicated expression than the one in our example, and these two expressions are not definitionally equal. This is why we prove equality using function extensionality rather than `rfl`.]
-/
example : pred = @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m)
:= by
  funext n
  cases n <;> rfl
/-
The first argument of `@Nat'.rec` is called the _motive_. The motive specifies the codomain of the resulting function; since this codomain may depend on the argument of the function, the motive itself is a function. In the case of `pred`, the codomain does not depend on the argument, and we can ignore the argument of the motive.

The second argument of `@Nat'.rec` tells how `zero` is mapped, and the third how `succ m` is mapped. The ignored argument in `(λ m _ ↦ m)` is the codomain given by the motive.


# Reduction of iota kind
%%%
tag := "sec-iota-reduction"
%%%

ι-reduction governs the interaction between recursors and constructors. It reduces applications of a recursor whose major premise is a constructor by selecting the corresponding minor premise.

Recall that the first argument of a recursor is called the motive. The last argument is called the _major premise_, and the remaining arguments are called the _minor premises_. There is one minor premise for each constructor of the underlying type.

-/
example :
  @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) zero = zero
:= rfl

#reduce @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) zero
#reduce zero
/-
Here the major premise is `zero`, corresponding to the _first_ constructor of `Nat'`. Accordingly, ι-reduction selects the _first_ minor premise, namely `zero`.

-/
variable (n : Nat')

example :
  @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) (succ n) = n
:= rfl

#reduce @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) (succ n)
#reduce n
/-
Here the major premise is `succ n`, corresponding to the _second_ constructor of `Nat'`. Accordingly, ι-reduction selects the _second_ minor premise `λ m _ ↦ m`, which is then applied to the argument `n` of the major premise.

Together with β- and δ-reductions, ι-reduction enables the following.
-/
example : pred zero = zero := rfl
example : pred (succ n) = n := rfl

#reduce pred zero
#reduce pred (succ n)
/-


# Structures
%%%
tag := "sec-structures"
%%%


At the level of Lean's type theory, [structures][structures] are inductive types that have a single constructor and no indices. At the surface syntax level, keyword `structure` {index}[structure] offers a number of conveniences.

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

The constructor is named `mk` (by default), and it has the fields `fst : α` and `snd : β` as given in the definition. Therefore, the above structure declaration yields the same constructor as our earlier definition of `Prod`.

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

The fields of a structure can be accessed by indices.
-/
example
  (α : Type u) (β : Type v) (p : Prod α β)
  : p.fst = p.1
:= rfl
/-

Structures also support record-style notation.
-/
example
  (α : Type u) (β : Type v) (a : α) (b : β) :
  Prod α β := {
    fst := a
    snd := b
  }
/-

If an inductive type has a single constructor, then this constructor is eligible for the [anonymous constructor syntax][anon-const-syntax] `⟨...⟩`. {index}[`⟨...⟩`] This syntax can be used, in particular, with structures.

[anon-const-syntax]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#anonymous-constructor-syntax

-/
example
  (α : Type u) (β : Type v) (a : α) (b : β)
  : Prod.mk a b = ⟨a, b⟩
:= rfl
/-


# Structure eta-equivalence

{ref "sec-function-eta-equivalence"}[Recall] that function η-equivalence identifies a function with the λ-abstraction obtained by applying it to an argument.

There is an analogous η-equivalence for structures. If the type of an expression `x` is a structure with two fields, then `x` is definitionally equal to the expression obtained by reconstructing it from its projections, namely `⟨x.1, x.2⟩`.

More generally, structure η-equivalence applies to structures with any number of fields. It also applies to any inductive type that could be defined as a structure, regardless of whether the surface-syntax keyword `structure` was used in its definition.

-/
variable (x : Demo.Prod ℕ ℕ)

example : ⟨x.1, x.2⟩ = x := rfl
/-

Written without syntactic sugar, this is
-/
example : Demo.Prod.mk x.1 x.2 = x := rfl
/-
The definitional equality of the left and right-hand sides is not based on them having the same normal form. In fact, their normal forms differ, as can be observed using `#reduce`.
-/
#reduce Demo.Prod.mk x.1 x.2
#reduce x
/-



# Further proofs and remarks

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
