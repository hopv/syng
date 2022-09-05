# Syho

**Syho** is a **separation logic** with **syntactically higher-order ghost
states**.

Syho supports **higher-order ghost states** (or **impredicative resources**),
bringing powerful expressivity, just like an existing separation logic
[**Iris**](https://iris-project.org/).

But in contrast to Iris's *fully semantic* approach, Syho models the
higher-order ghost states simply using the logic's **syntax** (for propositions
and judgments).

As a result, while Iris suffers from *step indexing* everywhere, Syho is **not
step-indexed at all**.  
Thanks to that, Syho has intuitive, easy-to-extend semantics and can flexibly
support **termination-sensitive** program reasoning.

Syho is mechanized in [**Agda**](https://agda.readthedocs.io/en/latest/), a
modern, dependently typed programming language.  
Agda is chosen here rather than [Coq](https://coq.inria.fr/),
[Lean](https://leanprover.github.io/), etc., because Agda has excellent support
of coinduction enabled by
[**sized types**](https://agda.readthedocs.io/en/latest/language/sized-types.html),
and Syho's approach takes great advantage of that.

## Getting Started

Just [install Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html).
Syho is known to work with Agda 2.6.2.2.  
Syho has no dependencies on external libraries.

For viewing and editing Agda code, you can use **Agda mode**
for [Emacs](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
or [VS Code](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode).

### Fonts

Syho's source code uses a lot of Unicode characters.  
To render them beautifully, we recommend you use monospace Unicode fonts that
support these characters, such as the following:
- [**JuliaMono**](https://juliamono.netlify.app/) ― Has a huge Unicode cover,
    including all the characters used in Syho's source code.
- [**Menlo**](https://en.wikipedia.org/wiki/Menlo_(typeface)) ― Is preinstalled
    on Mac and pretty beautiful. Doesn't support some characters (e.g., `⊢`).

For example, in VS Code, you can use the following setting (in `settings.json`)
to use Menlo as the primary font and fill in some gaps with JuliaMono.
```json
"editor.fontFamily": "Menlo, JuliaMono"
```

### Learning Agda

You can learn Agda's language features from
[the official document](https://agda.readthedocs.io/en/latest/language/index.html).

Here are notable features used in Syho.
- [**Sized types**](https://agda.readthedocs.io/en/latest/language/sized-types.html) ―
    Enable flexible coinduction, especially in combination with
    [thunks](src/Base/Thunk.agda).
- [**With-abstractions**](https://agda.readthedocs.io/en/latest/language/with-abstraction.html) ―
    Allow case analysis on calculated values.
- [**Copatterns**](https://agda.readthedocs.io/en/latest/language/copatterns.html) ―
    Get access to a component of records like a pattern.
- [**Record modules**](https://agda.readthedocs.io/en/latest/language/record-types.html#record-modules) ―
    Extend record types with derived notions, effectively used by the type
    [`ERA`](src/Syho/Model/ERA/Base.agda).

## Source Code

In the folder [`src`](src/) is the Agda source code for Syho.

### [`Base/`](src/Base/)

In [`Base/`](src/Base/) is a general-purpose library (though newly developed for
Syho).
Some of them re-export Agda's built-in libraries, possibly with renaming.
The library consists of the following parts.

- Basics ―
    [`Level`](src/Base/Level.agda) for universe levels;
    [`Func`](src/Base/Func.agda) for functions;
    [`Few`](src/Base/Eq.agda) for two-, one- and zero-element sets;
    [`Eq`](src/Base/Eq.agda) for equality;
    [`Size`](src/Base/Size.agda) for sizes (modeling ordinals);
    [`Thunk`](src/Base/Thunk.agda) for thunks.
- Data types ―
    [`Prod`](src/Base/Prod.agda) for sigma and product types;
    [`Sum`](src/Base/Sum.agda) for sum types;
    [`Option`](src/Base/Option.agda) for option types;
    [`List`](src/Base/List.agda) and [`List/`](src/Base/List/) for singly linked
    lists;
    [`Bool`](src/Base/Bool.agda) for Booleans;
    [`Dec`](src/Base/Dec.agda) for decidability.
- Numerics ―
    [`Nat`](src/Base/Nat.agda) for natural numbers;
    [`NatPos`](src/Base/NatPos.agda) for positive natural numbers;
    [`RatPos`](src/Base/RatPos.agda) for positive rational numbers;
    [`Natmap`](src/Base/Natmap.agda) for maps over natural numbers.

### [`Syho/`](src/Syho/)

In [`Syho/`](src/Syho/) is the heart of Syho, which consists of the following
parts.
- [`Lang/`](src/Syho/Lang/) ― Target language of Syho.
    + [`Expr`](src/Syho/Lang/Expr.agda) for addresses, types and expressions;
        [`Ktxred`](src/Syho/Lang/Ktxred.agda) for evaluation contexts and
        redexes;
        [`Reduce`](src/Syho/Lang/Reduce.agda) for the memory model and
        reduction of expressions.
    + [`Example`](src/Syho/Lang/Example.agda) for examples.
- [`Logic/`](src/Syho/Logic/) ― Syntax of the separation logic Syho.
    + [`Prop`](src/Syho/Logic/Prop.agda) for propositions;
        [`Judg`](src/Syho/Logic/Judg.agda) for judgments.
    + [`Core`](src/Syho/Logic/Core.agda) for core proof rules;
        [`Supd`](src/Syho/Logic/Supd.agda) for super updates;
        [`Ind`](src/Syho/Logic/Ind.agda) for the indirection modality and
        precursors;
        [`Hor`](src/Syho/Logic/Supd.agda) for Hoare triples.
    + [`Paradox`](src/Syho/Logic/Paradox.agda) for paradoxes on plausible proof
        rules.
    + [`Example`](src/Syho/Logic/Example.agda) for examples.
- [`Model/`](src/Syho/Model/) ― The semantic model and soundness proof of Syho.
    + [`Lib/`](src/Syho/Model/Lib) ― Libraries.
        * [`Exc`](src/Syho/Model/Lib/Exc.agda) for exclusivity boxes
    + [`ERA/`](src/Syho/Model/ERA/) ― Environmental resource algebras (ERAs),
        for modeling ghost states of Syho.
        * [`Base`](src/Syho/Model/ERA/Base.agda) for the basics of the ERA;
            [`Top`](src/Syho/Model/ERA/Top.agda) for the trivial ERA;
            [`Ind`](src/Syho/Model/ERA/Ind.agda) for the indirection ERAs;
            [`Glob`](src/Syho/Model/ERA/Glob.agda) for the global ERA.
    + [`Prop/`](src/Syho/Model/Prop/) ― the semantic model of propositions.
        * [`Base`](src/Syho/Model/Prop/Base.agda) for core logic connectives.
        * [`Basic`](src/Syho/Model/Prop/Basic.agda) for interpreting basic
            propositions;
            [`Ind`](src/Syho/Model/Prop/Ind.agda) for the indirection modality
            and precursors.
        * [`Interp`](src/Syho/Model/Prop/Interp.agda) for interpreting all
            propositions;
            [`Pure`](src/Syho/Model/Prop/Basic.agda) for semantic soundness of
            the pure sequent.
    + [`Supd/`](src/Syho/Model/Supd/) ― the semantic model of the super update.
        * [`Base`](src/Syho/Model/Supd/Base.agda) ― General super update
            modality.
        * [`Ind`](src/Syho/Model/Supd/Ind.agda) ― Super update modality on the
            indirection modality and precursors.
