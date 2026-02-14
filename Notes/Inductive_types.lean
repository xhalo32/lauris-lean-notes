/-
Inductive types
-/
import Mathlib
/-
%%%
tag := "sec-inductive-types"
%%%


[Inductive types][inductive-types] are the primary way to define new types in Lean. Type {lean}`Nat` of natural numbers is an example of an inductive type. Let's use the meta command `#print` {index}[#print] to inspect the definition of {lean}`Nat`.

[inductive-types]: https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/

-/
#print Nat
/-
The output shows the type constructor `Nat : Type`, followed by two constructors:

* `Nat.zero : ℕ` is a constant of type ℕ,{margin}[Recall that ℕ is shorthand for {lean}`Nat`.] and
* `Nat.succ : ℕ → ℕ` is a function from ℕ to ℕ.

Let's define an inductive type of the same form. {index}[inductive]
-/
inductive Nat' : Type where
  | zero : Nat'
  | succ (n : Nat') : Nat'

#print Nat'
/-

If the type signature of the type constructor is omitted, Lean will attempt to infer it automatically. The same holds for the type signature of a constructor.
-/
namespace Demo

inductive Nat where
  | zero
  | succ (n : Nat)

end Demo

#print Demo.Nat
/-
We introduced the namespace `Demo` {index}[namespace] to avoid a clash with the existing name `Nat`.

The constant `Nat'.zero` corresponds to `0` and `Nat'.succ` is the [successor function][succ]. Type `Nat'` comes with a namespace that we can open. {index}[open] Then we can write `zero` instead of `Nat'.zero`.

[succ]: https://en.wikipedia.org/wiki/Successor_function

-/
open Nat'
example : Nat' := zero
example : Nat' := succ zero
example : Nat' := succ (succ zero)
/-
These expressions can be interpreted as 0, 1, and 2.
The only way to construct an expression of type `Nat'` is by repeatedly applying the constructors, starting from `zero`.


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

In contrast to `Nat`, whose type constructor is a constant, the type constructor of `Prod` is a function (as we have {ref "sec-functions-of-types"}[already] observed).
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

The recursor of `Nat'` is `Nat'.rec`. To get a glimpse on how `pred` is translated into an application of `Nat'.rec`, let us consider a function that is extensionally equal to `pred` and that uses `Nat'.rec` directly.
-/
example : pred = @Nat'.rec (λ _ ↦ Nat') zero (λ m _ ↦ m)
:= by
  funext n
  cases n <;> rfl
/-
The first argument of `@Nat'.rec` is called a motive. The motive specifies the codomain of the resulting function; since this codomain may depend on the argument of the function, the motive itself is a function. In the case of `pred`, the codomain does not depend on the argument, and we can throw away the argument of the motive.

The second argument of `@Nat'.rec` tells how `zero` is mapped, and the third how `succ m` is mapped. The ignored argument in `(λ m _ ↦ m)` is the motive evaluated at the argument of the resulting function.

In practice, `@Nat'.rec` is called via a couple of internal helper functions as exposed by printing the definition of `pred`, with some translations enabled, together with the definitions of the helper functions. These helper functions should be considered as Lean's internal implementation details.
-/
set_option pp.all true
#print pred
#print pred.match_1
#print Nat'.casesOn
set_option pp.all false
/-
Studying these expressions, we see that `pred` boils down to a rather complicated composition of λ-abstractions involving `zero`, `succ`, and `Nat'.rec`.

Recursors have function types.
-/
#print Nat'.rec
/-
However, the only way to obtain a recursor is to let one be generated by defining an inductive type.


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

The structure `Prod` has two fields `fst` and `snd`. Each field in a structure corresponds to an argument of its constructor. The constructor is named `mk`, unless a name is explicitly provided. Therefore, the above structure declaration yields the same constructor as the earlier definition of `Prod`.

For each field, a projection function is generated that extracts the field's value from the underlying type's constructor.
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


# Further proofs and remarks

-/
example : ℕ = Nat := rfl
example : 0 = Nat.zero := rfl
example : 1 = Nat.succ Nat.zero := rfl
example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl

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

example : (0 = 0) = Eq 0 0 := rfl
/-

The fields of a structure can also be accessed by indices.
-/
example
  (α : Type u) (β : Type v) (p : Prod α β)
  : p.fst = p.1
:= rfl
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
