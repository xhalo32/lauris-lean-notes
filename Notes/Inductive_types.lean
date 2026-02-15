/-
Inductive types
-/
import Mathlib
/-
%%%
tag := "sec-inductive-types"
%%%


[Inductive types][inductive-types] are the primary way to define new types in Lean. Type {lean}`Nat` of natural numbers is an example of an inductive type. Let's use `#print` {index}[#print] command to inspect the definition of {lean}`Nat`.

[inductive-types]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/

-/
#print Nat
/-
The output shows the _type constructor_ `Nat : Type`, followed by two _constructors_:

* `Nat.zero : ℕ` is a constant of type ℕ,{margin}[Recall that ℕ is shorthand for {lean}`Nat`.] and
* `Nat.succ : ℕ → ℕ` is a function from ℕ to ℕ.

In Lean, `Nat.succ` is the [successor function][succ].

[succ]: https://en.wikipedia.org/wiki/Successor_function

The numerals 0, 1, 2, ... are syntactic sugar for expressions composed from the constructors of `Nat`.
-/
example : 0 = Nat.zero := rfl
example : 1 = Nat.succ Nat.zero := rfl
example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl
/-

Periods separate components of hierarchical names. {index}[.] The notion of a hierarchical name is [overloaded][identifiers] in Lean, and it can mean:

1. a name in a namespace,
2. an application of a named function from the namespace of a type to an element of that type, or
3. a projection of a field from a structure.

[identifiers]: https://lean-lang.org/doc/reference/latest/Terms/Identifiers/#identifiers-and-resolution

In the first case, all but the final component of a hierarchical name constitute the [namespace][namespace], while the final component is the name itself. This case includes `Nat.zero` and `Nat.succ`, where the namespace is `Nat`, and the names are `zero` and `succ`, respectively.

[namespace]: https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#namespaces

A basic example of the second case is given by
-/
example : 1 = Nat.zero.succ := rfl
/-
and the general pattern is: if `a` has type `α`, then `a.name` may be interpreted as `α.name a`.

We will return to the third case below.

Let's define an inductive type of the same form as `Nat`. {index}[inductive]
-/
inductive Nat' : Type where
  | zero : Nat'
  | succ (n : Nat') : Nat'

#print Nat'
/-

We can open {index}[open] the namespace of `Nat'`, and then write `zero` instead of `Nat'.zero`.
-/
open Nat'
example : Nat' := zero
example : Nat' := succ zero
example : Nat' := succ (succ zero)
/-
The only way to construct an expression of type `Nat'` is by repeatedly applying the constructors, starting from `zero`.

If the type signature of the type constructor is omitted, Lean will attempt to infer it automatically. The same holds for the type signature of a constructor. {index}[namespace]
-/
namespace Demo

inductive Nat where
  | zero
  | succ (n : Nat)

end Demo

#print Demo.Nat
/-
We introduced the namespace `Demo` to avoid a clash with the existing name `Nat`. We can also use it to demonstrate hierarchical names further.
-/
example : Demo.Nat := Demo.Nat.zero
/-
The hierarchical name on the right-hand side refers to the name `zero` in the namespace `Demo.Nat`.


# Type constructors with arguments

The Cartesian product is an example of an inductive type with parameters.
-/
universe u v
namespace Demo

inductive Prod
  (α : Type u) (β : Type v) : Type (max u v)
  where
  | mk (fst : α) (snd : β) : Prod α β

end Demo
/-

In contrast to `Nat`, the type constructor of `Prod` is a function (as we have {ref "sec-functions-of-types"}[already] observed).
-/
example : Type u → Type v → Type (max u v) := Demo.Prod
/-
Evaluating the type constructor gives a type.
-/
example (α β : Type) : Type := Demo.Prod α β
/-

Earlier we considered the product of ℕ with itself and used the notation `(0, 1)`, which is syntactic sugar for `Prod.mk 0 1`.

Inductive type declarations are subject to a number of [well-formedness requirements][well-formedness-req]. The following invalid piece of code produces an error.

[well-formedness-req]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#well-formed-inductives

```lean +error
inductive Bad where
  | mk : (Bad → Bad) → Bad
```


# Indexed families of types

{ref "sec-definitional-equality-naive"}[Recall] that `a = a` is syntactic sugar for `Eq a a`.
-/
#print Eq

namespace Demo

inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

end Demo

#print Demo.Eq
/-
Observe the analogy with the Cartesian product: the type constructor `Eq` is a function, and the evaluation `Eq a a` gives a type. However, unlike `Prod α β`, where `α` and `β` are types, the parameter `a` in `Eq a a` is an expression of type `α`. Such parameters are called indices, and `Eq` is said to be an indexed family of types. The universe `α` is an implicit parameter of `Eq`.

The family `Eq` has a single constructor, `refl`, that takes one argument. As a result, we can construct types of the form `Eq a a` for any expression `a`, but we can not construct types of the form `Eq a b` where `a` and `b` are distinct expressions. In this way, `Eq` encodes the equality between expressions.


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
The predecessor function maps `zero` to `zero` and `n` of form `succ m` to `m`.


## Pattern matching via recursors

The recursor of `Nat'` is `Nat'.rec`. It has a function type.
-/
#print Nat'.rec
/-

To get a glimpse on how `pred` is translated into an application of `Nat'.rec`, let us consider a function that is extensionally equal to `pred` and that uses `Nat'.rec` directly.
-/
example : pred = @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m)
:= by
  funext n
  cases n <;> rfl
/-
The first argument of `@Nat'.rec` is called the _motive_. The motive specifies the codomain of the resulting function; since this codomain may depend on the argument of the function, the motive itself is a function. In the case of `pred`, the codomain does not depend on the argument, and we can throw away the argument of the motive.

The second argument of `@Nat'.rec` tells how `zero` is mapped, and the third how `succ m` is mapped. The ignored argument in `(λ m _ ↦ m)` is the codomain given by the motive.

In practice, `@Nat'.rec` is called via a couple of Lean's helper functions as exposed by printing the definition of `pred`, with some translations enabled, together with the definitions of the helper functions.
-/
set_option pp.all true
#print pred
#print pred.match_1
#print Nat'.casesOn
set_option pp.all false
/-
Studying these expressions, we see that `pred` boils down to a rather complicated composition of λ-abstractions involving `zero`, `succ`, and `Nat'.rec`.


# Reduction of form iota
%%%
tag := "sec-iota-reduction"
%%%

ι-reduction governs the interaction between recursors and constructors. It reduces applications of a recursor whose major premise is a constructor by selecting the corresponding minor premise.

Recall that the first argument of a recursor is called the motive. The last argument is called the _major premise_, and the remaining arguments are called the _minor premises_. There is one minor premise for each constructor of the underlying type.

-/
example :
  @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) zero = zero
:= rfl
/-
Here the major premise is `zero`, corresponding to the _first_ constructor of `Nat'`. Accordingly, ι-reduction selects the _first_ minor premise, namely `zero`.

-/
example (n : Nat') :
  @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m) (succ n) = n
:= rfl
/-
Here the major premise is `succ n`, corresponding to the _second_ constructor of `Nat'`. Accordingly, ι-reduction selects the _second_ minor premise `λ m _ ↦ m`, which is then applied to the argument `n` of the major premise.

Together with β- and δ-reductions, ι-reduction enables the following.
-/
example : pred zero = zero := rfl
example (n : Nat') : pred (succ n) = n := rfl
/-


# Structures

At the level of the underlying type theory, [structures][structures] are inductive types that have a single constructor and that are not indexed families. At the surface syntax level, keyword `structure` {index}[structure] offers a number of conveniences.

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

The structure `Prod` has two fields `fst` and `snd`. Each field in a structure corresponds to an argument of its constructor. The constructor is named `mk`, unless a name is explicitly provided. Therefore, the above structure declaration yields the same constructor as our earlier definition of `Prod`.

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

{ref "sec-function-eta-equivalence"}[Recall] that function η-equivalence identifies a function with the λ-abstraction that applies it to an argument.

There is an analogous η-equivalence for structures. If `x` is an expression whose type is a structure with two fields, then `x` is definitionally equal to the expression obtained by reconstructing it from its projections, namely `⟨x.1, x.2⟩`.

More generally, structure η-equivalence applies to structures with any number of fields. It also applies to any inductive type that could be defined as a structure, regardless of whether the surface-syntax keyword `structure` was used in its definition.

-/
example (x : Demo.Prod ℕ ℕ) : x = ⟨x.1, x.2⟩ := rfl
/-


# Further proofs and remarks

-/
example : (0, 1) = Prod.mk 0 1 := rfl

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

example : (zero = zero) = Eq zero zero := rfl

example : zero = zero := rfl
/-

Projections have have the expected types.
-/
example
  (α : Type u) (β : Type v) (p : Prod α β) :
  α := p.fst

example
  (α : Type u) (β : Type v) (p : Prod α β) :
  β := p.snd
/-

Distinct inductive types are not definitionally equal. The following invalid line of code produces a type mismatch error.
```lean +error
example : Nat = Nat' := rfl
```
-/
