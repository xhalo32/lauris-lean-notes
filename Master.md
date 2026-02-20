#doc (Manual) "Notes on Lean for mathematically minded" =>

%%%
authors := ["Lauri Oksanen (lauri.oksanen@helsinki.fi)"]
%%%


# Foundations


In this chapter, we consider the most important expressions in Lean 4, viewed as a language for writing [formal proofs][formal-proof].{margin}[We are omitting expressions related to [quotient types][quotient-types], and effectively considering a [sublanguage][sublanguage].] It is remarkable that this language, namely Lean's type theory, is highly expressive while consisting of only the following kinds of expressions:

[formal-proof]: https://en.wikipedia.org/wiki/Formal_proof
[quotient-types]: https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/#quotients
[sublanguage]: https://en.wikipedia.org/wiki/Sublanguage

* universes in the universe hierarchy; 
* functions as λ-abstractions, together with their types and evaluations; 
* type constructors, constructors, and recursors of inductive types. 

Since our primary goal is to study formal proofs using Lean, the universe of propositions at the bottom of the universe hierarchy plays a central role.


{include 2 Generated.Expressions}
{include 2 Generated.Functions}
{include 2 Generated.Inductive_types}


# Index

{theIndex}
