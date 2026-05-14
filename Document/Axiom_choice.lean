/-
Axiom of choice
%%%
tag := "sec-axiom-choice"
%%%
-/
import Mathlib
/-
-/
-- -show
namespace Document.Axiom_choice
/-

The axiom of choice supplies an expression inhabiting a type `α` given a proof that `α` is inhabited. This bypasses the {ref "sec-restricted-elimination"}[restricted elimination] constraint of `Exists`. Due to its non-constructive nature, functions using the axiom must be marked noncomputable.
-/
#print Classical.choice

noncomputable example (α : Sort u)
  (h : Nonempty α) :
  α := Classical.choice h
/-
Here `Nonempty` is an inductive type with a single parameter `α`. Its only constructor requires providing an expression inhabiting `α`.
-/
#print Nonempty

example : Sort u → Prop := Nonempty

example (α : Sort u) (a : α) :
  Nonempty α := Nonempty.intro a
/-

As expected, the following noncomputable function cannot be executed.
```lean +error
noncomputable def choose_Nat (n : ℕ) : ℕ :=
  Classical.choice ⟨n⟩

#eval choose_Nat 0
```


# Choosing with a predicate

An existential proof can be turned into an expression satisfying its predicate.
-/
noncomputable example (α : Sort u) (P : α → Prop)
  (h : ∃ x, P x) :
  α := Classical.choose h
/-
This choice is guaranteed to satisfy the predicate.{margin}[This can be proven by `grind` as well.]
-/
example (α : Sort u) (P : α → Prop)
  (h : ∃ x, P x)
  : P (Classical.choose h)
:= Classical.choose_spec h
/-

Let us define our own versions of `choose` and `choose_spec`. They are obtained as projections of an expression inhabiting `Subtype P`. Such an expression consists of a choice and a proof that it satisfies the predicate.
-/
noncomputable def indef_desc {α : Sort u} (P : α → Prop)
  (h : ∃ x, P x) :
  Subtype P :=
    Classical.choice (
      let ⟨x, hx⟩ := h
      Nonempty.intro (Subtype.mk x hx)
    )

noncomputable def choose {α : Sort u} {P : α → Prop}
  (h : ∃ x, P x) :
  α := (indef_desc P h).val

lemma choose_spec {α : Sort u} {P : α → Prop}
  (h : ∃ x, P x)
  : P (choose h)
:=
  (indef_desc P h).property
/-

The deconstruction in the definition of `indef_desc` is invalid when not passed to the axiom of choice. Indeed, the naked version violates the restricted elimination constraint of `Exists`.
```lean +error
noncomputable example {α : Sort u} (P : α → Prop)
  (h : ∃ x, P x) :
  Subtype P :=
    let ⟨x, hx⟩ := h
    Subtype.mk x hx
```

Due to proof irrelevance, `choose` depends only on the predicate, not on the existential proof.
-/
lemma choose_pf_irrel {α : Sort u} {P₁ P₂ : α → Prop}
  (h : P₁ = P₂) (h₁ : ∃ x, P₁ x) (h₂ : ∃ x, P₂ x)
  : choose h₁ = choose h₂
:=
  @Eq.rec _ P₁
    (λ P _ ↦ ∀ (h : ∃ x, P x), choose h₁ = choose h)
    (λ _ ↦ Eq.refl (choose h₁))
    _ h h₂
/-


# Classical logic

The law of excluded middle
-/
example (p : Prop) : Prop := p ∨ ¬p
/-
holds in [classical logic][classical-logic] but not in [intuitionistic logic][intuitionistic-logic]. The three mathematical axioms enable encoding of classical logic.

[classical-logic]: https://en.wikipedia.org/wiki/Classical_logic
[intuitionistic-logic]: https://en.wikipedia.org/wiki/Intuitionistic_logic

-/
lemma excluded_middle (p : Prop) : p ∨ ¬p
:= Classical.em p

#print axioms excluded_middle
/-

Proving the law of excluded middle from
propositional extensionality, functional extensionality, and the axiom of choice is called [Diaconescu's theorem][diaconescu]. We present a proof for our own versions of `Or` and `Not`.

[diaconescu]: https://en.wikipedia.org/wiki/Diaconescu%27s_theorem

-/
inductive False' : Prop

def Not' (p : Prop) := p → False'

inductive Or' (p q : Prop) : Prop where
  | inl (h : p) : Or' p q
  | inr (h : q) : Or' p q

inductive True' : Prop where
  | intro : True'
/-

The idea of the proof is to define two families of predicates `U` and `V`, parametrized by propositions `p`. The families are chosen so that

1. the existence of witnesses satisfying the predicates is trivial, and
2. the predicates coincide as functions when `p` holds.

The first property guarantees that `choose` gives `u` and `v` satisfying the predicates. The second, together with `choose_pf_irrel`, yields `p → (u = v)`.

Further, the families are constructed so that `p` holds or `u` and `v` are distinct. Hence, `p` holds, or the distinctness and `p → (u = v)` imply, using [modus tollens][modus-tollens], that `p` does not hold.

[modus-tollens]: https://en.wikipedia.org/wiki/Modus_tollens

Two families with the above properties are defined as follows.
-/
def U (p : Prop) (x : Prop) := Or' (x = True') p

def V (p : Prop) (x : Prop) := Or' (x = False') p
/-

The first property is formulated as two lemmas, one per family.
-/
lemma witness_U (p : Prop) :
  ∃ x, U p x
:=
  ⟨True', Or'.inl rfl⟩

lemma witness_V (p : Prop) :
  ∃ x, V p x
:=
  ⟨False', Or'.inl rfl⟩
/-

We now show the second property.
-/
lemma Up_eq_Vp {p : Prop}
  (h : p)
  : U p = V p
:=
  have (x : Prop) : U p x ↔ V p x :=
    ⟨λ _ ↦ Or'.inr h, λ _ ↦ Or'.inr h⟩
  have (x : Prop) : U p x = V p x := propext (this x)
  funext this
/-

Finally, we need two small results: modus tollens for `Not'`, and distinctness of `True'` and `False'`. In fact, `False'` is distinct from any inhabited proposition.
-/
lemma mt' {p q : Prop} (h₁ : p → q) (h₂ : Not' q) : Not' p
:=
  λ h ↦ h₂ (h₁ h)

lemma ne_false_of_inhabited {p : Prop}
  (h : p)
  : Not' (p = False')
:=
  λ heq ↦ Eq.subst (motive := id) heq h

lemma t_ne_f : Not' (True' = False')
:=
  ne_false_of_inhabited True'.intro
/-

We are now ready to prove the law of excluded middle.
-/
example (p : Prop) : Or' p (Not' p)
:=
  let u := choose (witness_U p)
  have hu : Or' (u = True') p := choose_spec (witness_U p)

  let v := choose (witness_V p)
  have hv : Or' (v = False') p := choose_spec (witness_V p)

  have h₁ (h : p) : (u = v) :=
    choose_pf_irrel (Up_eq_Vp h) (witness_U p) (witness_V p)

  match hu, hv with
  -- p holds ...
  | Or'.inr h, _ => Or'.inl h
  | _, Or'.inr h => Or'.inl h
  -- ... or u and v are distinct
  | Or'.inl hut, Or'.inl hvf =>
    have h₂ : Not' (u = v) :=
      λ h ↦ t_ne_f (calc
        True'
        _ = u := hut.symm
        _ = v := h
        _ = False' := hvf
      )
    -- Conclude by modus tollens
    Or'.inr (mt' h₁ h₂)
/-
Each of the three mathematical axioms appears in the proof: `u` and `v` are ultimately obtained from `Classical.choice` while `Up_eq_Vp` relies on both `propext` and `Quot.sound`.{margin}[Recall that `funext` uses `Quot.sound`.]


# Further proofs

Introducing `choose` as an axiom instead of `Classical.choice` would yield an equivalent system. Above we derived the former from the latter. Here is a converse derivation.
-/
noncomputable example (α : Sort u)
  (h : Nonempty α) : α
  :=
  let P : α → Prop := λ _ ↦ True
  have : ∃ x, P x :=
    let ⟨a⟩ := h
    ⟨a, trivial⟩
  choose this
