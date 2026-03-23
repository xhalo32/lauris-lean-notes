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
open Document.Peano
open Document.Type_classes
```
When Lean's elaborator encounters an expression with unexpected type, it attempts to automatically insert a coercion, that is, a function from the unexpected type to the expected type. The search of a suitable function is based on instance synthesis.

As an illustration, consider our version of natural numbers `Nat'`{margin}[We have imported our earlier definitions.]
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

We can now add expressions of types `Nat` and `Nat'`.
-/
example (x : Nat) (y : Nat') : Nat' := x + y

example (x : Nat') (y : Nat) : Nat' := x + y
/-


# Numeric literals

Coercions are not used to resolve numeric literals.
```lean +error
example : Nat' := 0
```

Instead, the numeric literal parser is guided by `OfNat` type class.
-/
instance (n : Nat) : OfNat Nat' n where
  ofNat := n

example : Nat' := 0
/-

We can now compute in `Nat'` using numeric literals with type annotation.
-/
#reduce (2 : Nat')

example : (2 : Nat') + (2 : Nat') = (4 : Nat') := rfl
/-


-/
