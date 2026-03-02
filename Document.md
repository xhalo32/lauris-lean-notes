#doc (Manual) "Notes on Lean for mathematically minded" =>

%%%
shortTitle := "Notes on Lean"
shortContextTitle := "Notes"
authors := ["Lauri Oksanen"]
authorshipNote := "lauri.oksanen@helsinki.fi"
%%%


# Foundations

We will consider Lean's type theory as a language for writing [formal proofs][formal-proof]. It is remarkable that this language is highly expressive while consisting of only a few kinds of expressions.{margin}[We omit below expressions related to [quotient types][quotient-types], and effectively consider a [sublanguage][sublanguage].] 

Every type is either a universe in the universe hierarchy, a function type, or arises from the type constructor of an inductive type. The remaining expressions can be organized along two axes: 

```
<!--HTML-->
<table class="custom-concepts-2d">
  <thead>
    <tr><th></th><th>creation</th><th>elimination</th></tr>
  </thead>
  <tbody>
    <tr><th>function</th><td><code class="math inline">\lambda</code> abstraction</td><td>evaluation</td></tr>
    <tr><th>inductive type</th><td>constructor</td><td>recursor</td></tr>
  </tbody>
</table>
```

We begin with an introduction to types and universes. Since our primary goal is to study formal proofs using Lean, the universe of propositions at the bottom of the universe hierarchy plays a central role. The remainder of the chapter then proceeds through functions and inductive types. 

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
