import Mathlib
/-

# Lists

Lists are [tuples][tuple] of varying length.

[tuple]: https://en.wikipedia.org/wiki/Tuple

We define our version.
-/
#print List

inductive List' (α : Type) where
  | nil : List' α
  | cons (head : α) (tail : List' α) : List' α
/-

The standard version comes with syntactic sugar.
-/
example (α : Type) : [] = (List.nil : List α) := rfl

example (α : Type) (a : α) : a :: [] = List.cons a [] := rfl

example : 1 :: [] = [1] := rfl

example : 1 :: [2, 3] = [1, 2, 3] := rfl
/-

Lists can be concatenated.
-/
def List'.append {α : Type} : (xs ys : List' α) → List' α
  | nil,       bs => bs
  | cons a as, bs => cons a (List'.append as bs)
/-

The standard version comes with syntactic sugar.
-/
example (α : Type) (xs ys : List α) :
  xs.append ys = xs ++ ys := rfl

example : [1, 2] ++ [3, 4] = [1, 2, 3, 4] := rfl
/-

`(List α, ++, [])` is a monoid.
-/
instance (α : Type) : Monoid (List α) where
  mul := List.append
  one := List.nil
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil
/-

Show that `List' α` is a monoid in the same sense.
-/
lemma List'.append_nil {α : Type} (xs : List' α)
  : append xs nil = xs
:= by
  induction xs with
  | nil => rfl
  | cons a as hi => simp [append, hi]

lemma List'.append_assoc {α : Type} (xs ys zs : List' α)
  : (xs.append ys).append zs = xs.append (ys.append zs)
:= by
  -- __Solution__
  induction xs with
  | nil => rfl
  | cons a as hi => simp [append, hi]

instance (α : Type) : Monoid (List' α) where
  mul := List'.append
  one := List'.nil
  mul_assoc := List'.append_assoc
  mul_one := List'.append_nil
  one_mul := by
    intros
    rfl
/-

We define the sum of a list of natural numbers.
-/
def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

#eval sum [1, 2, 3]
/-

Show that `sum` is a monoid homomorphism.
-/
example (xs ys : List Nat)
  : sum (xs ++ ys) = sum xs + sum ys
:= by
  induction xs with
  | nil => simp [sum]
  | cons x xs hi =>
    simp [sum, hi]
    grind

example : sum [] = 0 := by rfl
/-

Show that the sum of a list of even numbers is even.
-/
def AllEven : List Nat → Prop
  | [] => True
  | x :: xs => x % 2 = 0 ∧ AllEven xs

example (xs : List Nat)
  (h : AllEven xs)
  : sum xs % 2 = 0
:= by
  -- __Solution__
  induction xs with
  | nil => simp [sum]
  | cons x xs hi =>
    simp [AllEven] at h
    simp [sum]
    grind
/-


# Reflexive transitive closure

The reflexive transitive closure of a relation is encoded as an inductive type.
-/
#print Relation.ReflTransGen
/-

We define our own version.
-/
inductive ReflTransGen' {α : Type}
  (r : α → α → Prop) (a : α) : α → Prop
  where
  | refl : ReflTransGen' r a a
  | tail {b c : α} :
    ReflTransGen' r a b → r b c → ReflTransGen' r a c
/-

We define `≤` on `Nat'` in two ways.
-/
inductive Nat' : Type where
  | zero : Nat'
  | succ : Nat' → Nat'

inductive Nat'.le (n : Nat') : Nat' → Prop
  | refl : n.le n
  | step {m : Nat'} : n.le m → n.le m.succ

inductive Nat'.le_step : Nat' → Nat' → Prop
  | mk {n : Nat'} : Nat'.le_step n n.succ

def Nat'.le' := ReflTransGen' Nat'.le_step
/-

Let us show that `le'` and `le` coincide.
-/
open ReflTransGen' Nat' in
example (n m : Nat') : (n.le' m) ↔ (n.le m) := by
  constructor
  · intro h
    induction h with
    | refl => exact le.refl
    | tail _ hstep hi =>
      cases hstep
      exact le.step hi
  · intro h
    -- __Solution__
    induction h with
    | refl => exact refl
    | step _ hi => exact tail hi le_step.mk
/-

Here is a more explicit proof of the implication from left to right.
-/
open ReflTransGen' Nat' in
example (n m : Nat') : (n.le' m) → (n.le m) := by
  intro h
  induction h with
  | refl => exact le.refl
  | @tail x y _ hxy hi =>
    cases hxy
    exact @le.step n x hi
/-


# MU puzzle

The [MU puzzle][MU] involves a simple formal language called MIU.

[MU]: https://en.wikipedia.org/wiki/MU_puzzle

The words in MIU language consists of letters M, I, and U.
-/
namespace MIU
inductive Letter | M | I | U
open Letter
/-

MIU language has one axiomatic word.
-/
def ax : List Letter := [M, I]
/-

We will encode MIU language using the reflexive transitive closure of the transformation rules
-/
inductive Step : List Letter → List Letter → Prop
  | r1 {x : List Letter} :
    Step (x ++ [I]) (x ++ [I, U])
  | r2 {x : List Letter} :
    Step ([M] ++ x) ([M] ++ x ++ x)
  | r3 {x y : List Letter} :
    Step (x ++ [I, I, I] ++ y) (x ++ [U] ++ y)
  | r4 {x y : List Letter} :
    Step (x ++ [U, U] ++ y) (x ++ y)
open Step
/-

The words in MIU are defined by
-/
def Word (w : List Letter) : Prop :=
  Relation.ReflTransGen Step ax w
open Relation.ReflTransGen
/-

Show that MIU is a word.
-/
example : Word [M, I, U] := by
  have : Word [M, I] := refl
  have : Word [M, I, U] := tail this (r1 (x := [M]))
  exact this
/-

Let's add a bit of syntactic sugar.
-/
infix:50 "⇒" => Relation.ReflTransGen Step
/-

A single step transformation can now be written
-/
example : [M, I] ⇒ [M, I, U] := tail refl (r1 (x := [M]))
/-

Or more shortly using
-/
#print single

example : [M, I] ⇒ [M, I, U] := single (r1 (x := [M]))
/-

Since the relation `⇒` is transitive, we can use it in a `calc` block.
-/
example : Word [M, I, U] := by
  calc
    [M, I]
    _ ⇒ [M, I, U] := single (r1 (x := [M]))
/-

Show that MIIII is a word.
-/
example : Word [M, I, I, I, I] := by
  calc
    [M, I]
    _ ⇒ [M, I, I] := single r2
    _ ⇒ [M, I, I, I, I] := single r2
/-

Show that MUI is a word.
-/
example : Word [M, U, I] := by
  -- __Solution__
  calc
    [M, I]
    _ ⇒ [M, I, I] := single r2
    _ ⇒ [M, I, I, I, I] := single r2
    _ ⇒ [M, U, I] := single (r3 (x := [M]))
/-

We are now ready for the actual puzzle: show that MU is not a word.

This puzzle might be hard to approach if you haven't seen similar ideas previously. You may want to read the solution in Wikipedia and focus only on formalizing it.

-/
-- __Solution__
def countI : List Letter → Nat
  | [] => 0
  | I :: xs => 1 + countI xs
  | M :: xs => countI xs
  | U :: xs => countI xs

lemma countI_append (xs ys : List Letter) :
  countI (xs ++ ys) = countI xs + countI ys
:= by
  induction xs with
  | nil => simp [countI]
  | cons x _ hi =>
    cases x <;> (
      simp [countI, hi]
      try grind
    )

lemma countI_invariant {w : List Letter} (hw : Word w)
  : countI w % 3 ≠ 0
:= by
  induction hw with
  | refl => simp [ax, countI]
  | tail _ hs hi =>
    cases hs <;> (
      simp [countI_append, countI] at *
      grind
    )

example : ¬Word [M, U] := by
  intro h
  have := countI_invariant h
  simp [countI] at this
