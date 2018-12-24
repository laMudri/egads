# Egads!

> [P]: Gee Brain, what d'you wanna do tonight?  
> [B]: Same thing we do every night, Pinky: try to formalise category theory!

Egads is a library where I define some category theory concepts and prove some elementary results.
It's mainly for my own learning, but it might be somehow useful.

`Category` is the type of [E-categories][ecats] (categories where the objects form a type but the homs form setoids).
This is possibly the final fling for E-categories before the cubical revolution.
The `Category` definition is built up over many tiers with the intent of making definitions that read like “a *monoid* is a category with a single object”.
These should be transparent (intensionally) to the users of `Monoid`.
I have a couple of examples in `Egads.Structure`, and aim to add ring-like structures with the help of enriched categories.

This library depends on a few modules of stdlib.
So far, this is:

* `Data.Product`
* `Data.Product.Relation.Pointwise.NonDependent` (including some definitions [not yet in a release](https://github.com/agda/agda-stdlib/pull/572))
* `Data.Unit`
* `Function`
* `Function.Equality`
* `Relation.Binary`
* `Relation.Binary.EqReasoning`
* `Relation.Binary.On`
* `Relation.Binary.PropositionalEquality`
* `Relation.Binary.SetoidReasoning`

It wouldn't be too much work to replicate the definitions used here (yet, at least).
The major incompatibility with stdlib is that I want to redo stdlib's algebra and order definitions to be categorial.

[ecats]: https://arxiv.org/abs/1408.1364
