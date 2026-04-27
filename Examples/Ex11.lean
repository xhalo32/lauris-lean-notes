import Mathlib
/-

# Trileans

Consider trileans with a natural coercion to integers, as used in [Kleene and Priest logics][kleene-priest].

[kleene-priest]: https://en.wikipedia.org/wiki/Three-valued_logic#Kleene_and_Priest_logics

-/
inductive Trilean where
  | F
  | U
  | T
deriving DecidableEq

def Trilean.toInt (x : Trilean) : ℤ :=
  match x with
  | F => -1
  | U => 0
  | T => 1

instance : Coe Trilean ℤ where
  coe := Trilean.toInt
/-

We define a left inverse of `Trilean.toInt`.
-/
def Trilean.ofInt (x : ℤ) : Trilean :=
  match x with
  | -1 => F
  | 1 => T
  | _ => U
/-

Show that `Trilean.ofInt` is indeed a left inverse of `Trilean.toInt`.
-/
open Trilean in
example : ofInt ∘ toInt = id
:= by
  -- __Solution__
  funext x
  cases x <;> rfl
/-

Define a coercion from `ℤ` to `Trilean` using `Trilean.ofInt`.
-/
-- __Solution__
instance : Coe ℤ Trilean where
  coe := Trilean.ofInt
/-

We define a multiplication on `Trilean` by [transporting][transport] the multiplicative structure of `ℤ` using `Trilean.toInt` and `Trilean.ofInt`.

[transport]: https://en.wikipedia.org/wiki/Transport_of_structure

-/
instance : Mul Trilean where
  mul x y := Trilean.ofInt (x.toInt * y.toInt)
/-

Show that `Trilean` is a monoid.
-/
instance : Monoid Trilean where
  one := Trilean.T
  mul_assoc := by
    -- __Solution__
    intro x y z
    cases x <;> cases y <;> cases z <;> rfl
  one_mul := by
    -- __Solution__
    intro x
    cases x <;> rfl
  mul_one := by
    -- __Solution__
    intro x
    cases x <;> rfl
/-

Show that `Trilean.toInt` is a monoid homomorphism.
-/
example : Trilean →* ℤ where
  toFun := Trilean.toInt
  map_one' := by
    -- __Solution__
    rfl
  map_mul' := by
    -- __Solution__
    intro x y
    cases x <;> cases y <;> rfl
/-

Show that `U` does not have an inverse, implying that `Trilean` is not a [group][group].

[group]: https://en.wikipedia.org/wiki/Group_(mathematics)

-/
open Trilean in
example : ¬ ∃ x, x * U = T := by
  -- __Solution__
  simp
  intro x
  cases x <;> decide
