/-
Coercions
%%%
tag := "sec-coercions"
%%%
-/
import Mathlib
import Document.Type_classes
/-
```lean -show
open Document.Type_classes
```
When Lean's elaborator encounters an expression with unexpected type, it attempts to automatically insert a coercion, that is, a function from the unexpected type to the expected type. The search of a suitable function is based on instance synthesis.

As an illustration, consider our version of natural numbers `Nat'`. We have [imported][import] {index}[`import`] our earlier definitions, and have also the `+` notation at our use.{margin}[In the example, `Nat'` is a link that takes to its definition.]

[import]: https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-headers
-/
example (x y : Nat') : Nat' := x + y
/-

The following invalid example triggers the coercion mechanism, but instance synthesis fails to find a coercion.
```lean +error
example (x : Nat) (y : Nat') : Nat' := x + y
```

We can define a coercion from `Nat` to `Nat'` using `Coe` type class.
-/
def Nat'.ofNat (n : Nat) : Nat' :=
  match n with
  | 0 => Nat'.zero
  | n + 1 => (Nat'.ofNat n).succ

instance : Coe Nat Nat' where
  coe := Nat'.ofNat
/-

Now we can add expression of types `Nat` and `Nat'`.
-/
example (x : Nat) (y : Nat') : Nat' := x + y

example (x : Nat') (y : Nat) : Nat' := x + y
/-


# Numeric literals

Coercions are not used to resolve numeric literals.
```lean +error
example : Nat' := 0
```

Instead, the numeric literal parser is guided by the `OfNat` type class.
-/
instance (n : Nat) : OfNat Nat' n where
  ofNat := n

example : Nat' := 0
/-

Now we can compute in `Nat'` using numeric literals.
-/
#reduce (2 : Nat')

example : (2 : Nat') = (1 : Nat') + (1 : Nat') := rfl
