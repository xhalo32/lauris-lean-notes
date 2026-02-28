#doc (Manual) "Notes on Lean for mathematically minded" =>

%%%
shortTitle := "Notes on Lean"
shortContextTitle := "Notes"
authors := ["Lauri Oksanen"]
authorshipNote := "lauri.oksanen@helsinki.fi"
%%%


# Foundations

In this chapter, we consider the most important expressions in Lean 4, viewed as a language for expressing [formal proofs][formal-proof]. It is remarkable that this language, namely Lean's type theory, is highly expressive while consisting of only a few kinds of expressions.{margin}[We are omitting expressions related to [quotient types][quotient-types], and effectively considering a [sublanguage][sublanguage].] All types are either 

* universes in the universe hierarchy,
* function types, or
* given by type constructors of inductive types.

The remaining expressions can be organized along two axes as follows: 

```
<!--HTML-->
<table class="custom-concepts-2d">
  <thead>
    <tr><th></th><th>creation</th><th>elimination</th></tr>
  </thead>
  <tbody>
    <tr><th>function</th><td>λ-abstraction</td><td>evaluation</td></tr>
    <tr><th>inductive type</th><td>constructor</td><td>recursor</td></tr>
  </tbody>
</table>
```

We begin with an introduction to expressions, types and universes. Since our primary goal is to study formal proofs using Lean, the universe of propositions at the bottom of the universe hierarchy plays a central role. The remainder of the chapter then proceeds through functions and inductive types. 

[formal-proof]: https://en.wikipedia.org/wiki/Formal_proof
[quotient-types]: https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/#quotients
[sublanguage]: https://en.wikipedia.org/wiki/Sublanguage

{include 2 Document.Expressions}
{include 2 Document.Functions}
{include 2 Document.Inductive_types}


# Constructions

{include 2 Document.Equality}


# Index

{theIndex}
