/-
Type classes
%%%
tag := "sec-type-classes"
%%%
-/
import Mathlib
import Document.Peano
/-
One of the simplest type classes is `Add`.
-/
#print Add
/-

Like structures, type classes are a feature at the elaboration stage. We define our version of `Add`. {index}[`class … where`]
-/
class Add' (α : Type u) where
  add : α → α → α
/-
The `class` declaration results in formation of an inductive type with a single constructor called `mk`, just as if `structure` had been used instead.
-/
example (α : Type u) : Type u := Add' α

example :
  (α : Type u) /- parameter -/ →
  (α → α → α) /- field (add) -/ →
  Add' α /- codomain -/
:= @Add'.mk
/-

Let us return to our version of natural numbers `Nat'`, and define an instance `Add' Nat`. We have [imported][import] {index}[`import`] our earlier definitions.{margin}[In the next example, `Nat'` is a link that takes to its definition.] The syntax of instance declarations is similar to that of record-style definitions, such as

[import]: https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-headers

-/
def origin : Prod ℕ ℕ where
  fst := 0
  snd := 0
/-

Indeed, {index}[`instance … where`]
-/
instance Nat'.instAdd' : Add' Nat' where
  add := Nat'.add

example : Add' Nat' := Nat'.instAdd'
/-

Giving a name is optional in instance declarations, and Lean's instance synthesis can search for an expression of a required type at the elaboration stage. Instance synthesis can be tested using `#synth` command. {index}[`#synth`]
-/
#synth Add' Nat'
/-

Type classes enable [ad-hoc polymorphism][ad-hoc-polymorphism]. As an illustration, we define _add in reverse order_ on `Add'`. {index}[`[…]`]

[ad-hoc-polymorphism]: https://en.wikipedia.org/wiki/Ad_hoc_polymorphism

-/
def Add'.addr {α : Type u} [Add' α] (x y : α) : α :=
  Add'.add y x
/-
Here `[Add' α]` denotes an implicit argument of type `Add' α`. Now `Add'.addr` can be used on `Nat'`.
-/
example (x y : Nat') : Nat' := Add'.addr x y

example (x y : Nat') : Add'.addr x y = Nat'.add y x := rfl
/-
In these two examples, Lean uses instance synthesis to supply an implicit argument of type `Add' Nat'`. The corresponding explicit versions read
-/
example (x y : Nat') : Nat' :=
  @Add'.addr Nat' Nat'.instAdd' x y

example (x y : Nat')
  : @Add'.addr Nat' Nat'.instAdd' x y = Nat'.add y x
:= rfl
/-


# Overloading

The type class `HAdd` is responsible for the `+` notation. It allows heterogeneous addition, where the domain and codomain may differ.
-/
#print HAdd

example (α β γ : Type) [HAdd α β γ]
  (a : α) (b : β) : a + b = HAdd.hAdd a b := rfl
/-

We can [overload][overloading] `+` notation for `Add'`.

[overloading]: https://en.wikipedia.org/wiki/Operator_overloading
-/
instance (α : Type u) [Add' α] : HAdd α α α where
  hAdd := Add'.add
/-

Now `+` can be used on `Nat'`
-/
example (x y : Nat') : Nat' := x + y

example (x y : Nat') : x + y = Nat'.add x y := rfl
/-


# Class hierarchy

The mathematical concept corresponding to `Add` is [magma][magma]. A [semigroup][semigroup] is a magma whose binary operation is associative. In Lean, there are parallel hierarchies for multiplication and addition. The two hierarchies are isomorphic from the mathematical point of view, only the notation differs. {index}[extends]

[magma]: https://en.wikipedia.org/wiki/Magma_(algebra)
[semigroup]: https://en.wikipedia.org/wiki/Semigroup

-/
#print Semigroup
#print AddSemigroup

class AddSemigroup' (G : Type u) extends Add' G where
  add_assoc : ∀ a b c : G, (a + b) + c = a + (b + c)
/-

All instances of `AddSemigroup'` are instances of `Add'`, that is, if there is an expression of type `AddSemigroup' G` then there is an expression of type `Add' G`. This can be shown using `inferInstance`.
-/
#print inferInstance

example (G : Type u) [AddSemigroup' G] : Add' G
:= inferInstance
/-

Constructing an expression of type `AddSemigroup' Nat'` amounts to providing a proof that `Nat'.add` is associative.{margin}[Recall that we have already shown the associativity. In the example, `add_assoc` is a link that takes to its definition.]
-/
instance : AddSemigroup' Nat' where
  add_assoc := @Nat'.add_assoc
/-

Mathlib has a rich hierarchy of classes. [Mathematics in Lean][mathematics-in-lean] gives an introduction to this hierarchy.

[mathematics-in-lean]: https://leanprover-community.github.io/mathematics_in_lean

-/
