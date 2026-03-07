#doc (Manual) "Notes on Lean" =>

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
    <tr><th>function</th><td><code class="math inline">\lambda</code>-abstraction</td><td>evaluation</td></tr>
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

We have now seen all the primitive notions in Lean's type theory. To reiterate, they are universes, function types, and inductive types,{margin}[We view `→` and `inductive … where` as primitive notions. This does not include concrete function types or inductive types.] together with creation and elimination of expressions of the latter two types. In addition, we have considered the concrete inductive types `Eq` and `Nat`, as well as the product and sum types `Prod` and `Sum`.

We begin with an encoding of first-order logic using inductive types. This involves [product][product-type] and [sum][sum-type] types similar to `Prod` and `Sum`, a [dependent sum type][dep-sum-type], a [unit type][unit-type] `⊤`, and an [empty type][empty-type] `⊥`. The remainder of the chapter then takes a deeper look at `Eq` and `Nat`.

[product-type]: https://en.wikipedia.org/wiki/Product_type
[sum-type]: https://en.wikipedia.org/wiki/Sum_type
[dep-sum-type]: https://en.wikipedia.org/wiki/Dependent_type#%CE%A3_type
[unit-type]: https://en.wikipedia.org/wiki/Unit_type
[empty-type]: https://en.wikipedia.org/wiki/Empty_type

{include 2 Document.Logic}
{include 2 Document.Equality}
{include 2 Document.Peano}


# Index

{theIndex}
