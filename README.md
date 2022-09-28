# Syho

**Syho** is a **concurrent separation logic** with **syntactically higher-order
ghost states**.

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
    Enable flexible coinduction and induction, especially in combination with
    [thunks and shrunks](src/Base/Size.agda).
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

In [`Base/`](src/Base/) is a **general-purpose library** (though newly developed
for Syho).
Some of them re-export Agda's built-in libraries, possibly with renaming.
The library consists of the following parts.

- **Basics** ―
    [`Level`](src/Base/Level.agda) for universe levels;
    [`Func`](src/Base/Func.agda) for functions;
    [`Few`](src/Base/Eq.agda) for two-, one- and zero-element sets;
    [`Eq`](src/Base/Eq.agda) for equality;
    [`Acc`](src/Base/Acc.agda) for accessibility;
    [`Size`](src/Base/Size.agda) for sizes (modeling ordinals), thunks and
        shrunks.
- **Data types** ―
    [`Prod`](src/Base/Prod.agda) for sigma and product types;
    [`Sum`](src/Base/Sum.agda) for sum types;
    [`Option`](src/Base/Option.agda) for option types;
    [`Dec`](src/Base/Dec.agda) for decidability;
    [`Inh`](src/Base/Inh.agda) for inhabitance;
    [`Zoi`](src/Base/Zoi.agda) for zoi (zero, one, or infinity) numbers;
    [`Nat`](src/Base/Nat.agda) for natural numbers;
    [`NatPos`](src/Base/NatPos.agda) for positive natural numbers;
    [`List`](src/Base/List.agda) for singly linked lists;
    [`Seq`](src/Base/Seq.agda) for infinite sequences;
    [`Str`](src/Base/Str.agda) for characters and strings;
    [`RatPos`](src/Base/RatPos.agda) for positive rational numbers.
- **Misc** ― [`Sety`](src/Base/Sety.agda) for syntactic sets.

### [`Syho/`](src/Syho/)

In [`Syho/`](src/Syho/) is **the heart of Syho**, which consists of the
following parts.
- [`Lang/`](src/Syho/Lang/) ― **The target language of Syho.**
    + [`Expr`](src/Syho/Lang/Expr.agda) for addresses, types and expressions;
        [`Ktxred`](src/Syho/Lang/Ktxred.agda) for evaluation contexts and
        redexes;
        [`Reduce`](src/Syho/Lang/Reduce.agda) for the memory model and
        reduction of expressions.
    + [`Example`](src/Syho/Lang/Example.agda) for examples.
- [`Logic/`](src/Syho/Logic/) ― **The syntax of the separation logic Syho.**
    + [`Prop`](src/Syho/Logic/Prop.agda) for propositions;
        [`Judg`](src/Syho/Logic/Judg.agda) for judgments.
    + [`Core`](src/Syho/Logic/Core.agda) for core proof rules;
        [`Supd`](src/Syho/Logic/Supd.agda) for super updates;
        [`Ind`](src/Syho/Logic/Ind.agda) for the indirection modality and the
        precursors;
        [`Hor`](src/Syho/Logic/Supd.agda) for Hoare triples.
    + [`Paradox`](src/Syho/Logic/Paradox.agda) for paradoxes on plausible proof
        rules.
    + [`Example`](src/Syho/Logic/Example.agda) for examples.
- [`Model/`](src/Syho/Model/) ― **The semantic model and soundness proof of
    Syho.**
    + [`ERA/`](src/Syho/Model/ERA/) ― **Environmental resource algebras (ERAs),
        for modeling ghost states of Syho.**
        * [`Base`](src/Syho/Model/ERA/Base.agda) for the basics of the ERA.
        * General ERAs ―
            [`Top`](src/Syho/Model/ERA/Top.agda) for the trivial ERA;
            [`Prod`](src/Syho/Model/ERA/Prod.agda) for the product ERA;
            [`All`](src/Syho/Model/ERA/All.agda) for the dependent-map ERA;
            [`Envm`](src/Syho/Model/ERA/Envm.agda) for the environment
            modification ERA;
            [`Envv`](src/Syho/Model/ERA/Envv.agda) for the environment
            validity ERA;
            [`Up`](src/Syho/Model/ERA/Up.agda) for the level-up ERA.
        * Basic ERAs ―
            [`Zoi`](src/Base/Zoi.agda) for the zoi ERA;
            [`Exc`](src/Syho/Model/ERA/Exc.agda) for the exclusive ERA;
            [`Ag`](src/Syho/Model/ERA/Ag.agda) for the agreement ERA;
            [`Frac`](src/Syho/Model/ERA/Frac.agda) for the fractional ERA.
        * Language-specific ERA ―
            [`Mem`](src/Syho/Model/ERA/Mem.agda) for the memory ERA.
        * Logic-dependent ERAs ―
            [`Ind`](src/Syho/Model/ERA/Ind.agda) for the indirection ERAs.
        * Global ERA ―
            [`Glob`](src/Syho/Model/ERA/Glob.agda) for the global ERA.
    + [`Prop/`](src/Syho/Model/Prop/) ― **The semantic model of the propositions
        and the semantic soundness of the pure sequent.**
        * [`Base`](src/Syho/Model/Prop/Base.agda) for the core semantic logic
            connectives;
            [`Smry`](src/Syho/Model/Prop/Smry.agda) for the map summary;
            [`Mem`](src/Syho/Model/Prop/Mem.agda) for interpreting the points-to
            and freeing tokens.
        * [`Basic`](src/Syho/Model/Prop/Basic.agda) for interpreting basic
            propositions;
            [`Ind`](src/Syho/Model/Prop/Ind.agda) for interpreting the
            indirection modality and precursors.
        * [`Interp`](src/Syho/Model/Prop/Interp.agda) for interpreting all the
            propositions;
            [`Sound`](src/Syho/Model/Prop/Sound.agda) for the semantic soundness
            of the logic's pure sequent.
    + [`Supd/`](src/Syho/Model/Supd/) ― **The semantic model and soundness proof
        of the super update.**
        * [`Base`](src/Syho/Model/Supd/Base.agda) for the general super update;
            [`Ind`](src/Syho/Model/Supd/Ind.agda) for the super update on the
            indirection modality and precursors.
        * [`Interp`](src/Syho/Model/Prop/Interp.agda) for interpreting the super
            update;
          [`Sound`](src/Syho/Model/Supd/Sound.agda) for the semantic soundness
            of the logic's super-update sequent.
    + [`Hor/`](src/Syho/Model/Hor/) ― **The semantic model and soundness proof
        of the partial and total Hoare triples.**
        * [`Wp`](src/Syho/Model/Hor/Wp.agda) for the semantic partial and total
            weakest preconditions;
          [`Lang`](src/Syho/Model/Hor/Lang.agda) for language-specific lemmas on
            the weakest preconditions;
          [`Mem`](src/Syho/Model/Hor/Mem.agda) for semantic super update and
            weakest precondition lemmas for the memory.
        * [`Sound`](src/Syho/Model/Hor/Sound.agda) for the semantic soundness of
            the logic's Hoare triple.
        * [`Adeq`](src/Syho/Model/Hor/Adeq.agda) for the adequacy of the
            semantic partial and total weakest preconditions.

## Meta-logic

As the meta-logic of Syho, we use **Agda**, under the option
**`--without-K --sized-types`**, **without any extra axioms**.

Our meta-logic has the following properties.
- We **use only predicative universes** and don't use any *impredicative
    universes* like Coq's `Prop`.
- We **don't use any classical or choice axioms**.
- We **don't use the axiom K**, an axiom incompatible with the **univalence**
    axiom.
- We don't use any proof-irrelevant types like types in Coq's `Prop`.
- We use **sized types** for coinduction, including the **inaccessible ordinal
    `∞`**.
    + Despite some concerns about Agda's soundness around sized types, we
        believe our usage of sized types in Syho's mechanization is safe.

## Termination verification

Syho has two types of Hoare triples, **partial** and **total**.  
The partial Hoare triple allows coinductive reasoning but does not ensure
termination.  
The total Hoare triple allows only inductive reasoning and thus ensures
termination.

### Comparison with step-indexed logics

This is in contrast to step-indexed logics like Iris:  
A Hoare triple can only be *partial*, because one *later modality* `▷` should be
stripped off per program step, and the later modality introduces coinductive
reasoning by Löb induction.

To see this, let's suppose that the target language has a constructor `▶` on an
expression, such that `▶ e` reduces to `e` in one program step.  
In such a step-indexed logic, because **one later modality is stripped off per
program step**, we have the following rule.
```
▷ { P } e { Q }  ⊢  { P } ▶ e { Q }
```
Intuitively, `▷ P`, `P` under the *later modality* `▷`, means that `P` holds
after one *logical* step.

Also, suppose that we can make a vacuous loop `▶ ▶ ▶ …` of `▶`s. Now we have the
following lemma.
```
▷ { P } ▶ ▶ ▶ … { Q }  ⊢  { P } ▶ ▶ ▶ … { Q }
```

On the other hand, a step-indexed logic has the following rule called **Löb
induction**.
```
▷ P → P  ⊢  P
```
If we can get `P` assuming `▷ P` (or intuitively, `P` after one logical step),
then we get `P` itself.

Combining this Löb induction with the previous lemma, we can have a Hoare triple
on `▶ ▶ ▶ …` without any premise.
```
⊢  { P } ▶ ▶ ▶ … { Q }
```
Because the loop `▶ ▶ ▶ …` does not terminate, this means that the Hoare triple
is partial, not total.  
Ultimately, this is due to the coinduction introduced by the later modality.

For this reason, Iris does not generally support termination verification (other
than by actually bounding the number of program steps).

Transfinite Iris (Spies et al., 2021), a variant of Iris with step-indexing over
ordinal numbers, supports *time credits with ordinals* for termination
verification.  
However, to use this, one should do careful math of ordinals, which is a
demanding task and formally requires classical and choice axioms.

Syho simply provides the **total** Hoare triple with **inductive** deduction,
thanks to Syho being **non-step-indexed**.  
Remarkably, we can **take advantage of Agda's termination checker** for
termination verification in Syho, which is handy, flexible and expressive.
