import Mathlib
/-

# Syntactic sugar

Consider the type
-/
example : Type := ℕ ⊕ ℕ
/-
Write `ℕ ⊕ ℕ` in reduced form without syntactic sugar.
-/
set_option pp.notation false in
#reduce ℕ ⊕ ℕ

example : (ℕ ⊕ ℕ) = (Sum Nat Nat) := rfl
/-

Consider the expression
-/
example (n : ℕ) : ℕ := n + 0
/-
Write `n + 0` in reduced form without syntactic sugar.
-/
variable (n : ℕ)
#reduce n + 0

example (n : ℕ) : n + 0 = n := rfl
/-

Show that `0` coincides with `Nat.zero`.
-/
example : 0 = Nat.zero := rfl
/-

Consider the expression
-/
example (n : ℕ) : ℕ := n + 1
/-
Write `n + 1` in reduced form without syntactic sugar.
-/
variable (n : ℕ)
#reduce n + 1

example (n : ℕ) : n + 1 = n.succ := rfl
/-

Show that `n + 1` for `n : ℕ` coincides with `Nat.succ n`.
-/
example (n : ℕ) : n + 1 = Nat.succ n := rfl
/-

Show that `1` coincides with `Nat.zero.succ`.
-/
example : 1 = Nat.zero.succ := rfl
/-

Consider the type
-/
example (p q : Prop) : Prop := p ∧ q
/-
Write `p ∧ q` in reduced form without syntactic sugar.
-/
variable (p q : Prop)
set_option pp.notation false in
#reduce p ∧ q

example : (p ∧ q) = (And p q) := rfl
/-

Consider the type
-/
example (p : Prop) : Prop := ¬p
/-
Write `¬p` in reduced form without syntactic sugar, forcing reduction inside types.
-/
variable (p : Prop)
set_option pp.notation false in
#reduce (types := true) ¬p

example : (¬p) = (p → False) := rfl
/-


# Components of nested pairs

Components of a pair can be extracted with indices.
-/
example (α β : Type) (a : α) (b : β)
  : (a, b).1 = a
:= rfl

example (α β : Type) (a : α) (b : β)
  : (a, b).2 = b
:= rfl
/-

Consider
-/
example (α β γ : Type) (a : α) (b : β) (c : γ)
  : ((a, b), c).1.1 = a
:= rfl
/-
Extract `b` and `c` from `((a, b), c)`.

-/
example (α β γ : Type) (a : α) (b : β) (c : γ)
  : ((a, b), c).1.2 = b
:= rfl

example (α β γ : Type) (a : α) (b : β) (c : γ)
  : ((a, b), c).2 = c
:= rfl
/-

Consider
-/
example (α β γ δ : Type) (a : α) (b : β) (c : γ) (d : δ)
  : ((a, b), (c, d)).1.1 = a
:= rfl
/-
Extract `b`, `c`, and `d` from `((a, b), (c, d))`.

-/
example (α β γ δ : Type) (a : α) (b : β) (c : γ) (d : δ)
  : ((a, b), (c, d)).1.2 = b
:= rfl

example (α β γ δ : Type) (a : α) (b : β) (c : γ) (d : δ)
  : ((a, b), (c, d)).2.1 = c
:= rfl

example (α β γ δ : Type) (a : α) (b : β) (c : γ) (d : δ)
  : ((a, b), (c, d)).2.2 = d
:= rfl
/-

Consider
-/
example (α β γ δ : Type) (a : α) (b : β) (c : γ) (d : δ)
  : (a, (b, (c, d))).1 = a
:= rfl
/-
Extract `b`, `c`, and `d` from `(a, (b, (c, d)))`.

-/
example (α β γ δ : Type) (a : α) (b : β) (c : γ) (d : δ)
  : (a, (b, (c, d))).2.1 = b
:= rfl

example (α β γ δ : Type) (a : α) (b : β) (c : γ) (d : δ)
  : (a, (b, (c, d))).2.2.1 = c
:= rfl

example (α β γ δ : Type) (a : α) (b : β) (c : γ) (d : δ)
  : (a, (b, (c, d))).2.2.2 = d
:= rfl
/-


# On universe hierarchy

Consider
-/
variable (α : Type u) (β : Type v)
/-

Find the type of `Prod α β`.
-/
#check Prod α β

example : Type (max u v) := Prod α β
/-

Find the type of `Sum α β`.
-/
#check Sum α β

example : Type (max u v) := Sum α β
/-

Find the type of `α → β`.
-/
#check α → β

example : Type (max u v) := α → β
/-

Consider
-/
variable (γ : Sort u) (δ : Sort v)
/-
Find the type of `γ → δ`.
-/
#check γ → δ

example : Sort (imax u v) := γ → δ
