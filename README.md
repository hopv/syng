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
[Lean](https://leanprover.github.io/), etc., because Syho's syntax takes
advantage of **coinduction** and Agda has a great support of coinduction by
[**sized types**](https://agda.readthedocs.io/en/latest/language/sized-types.html).

## Installation

1. [Install Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html).

That's all!

We have checked that Syho works with Agda 2.6.2.2.

## Learning Agda

You can learn Agda's language features by
[the official document](https://agda.readthedocs.io/en/latest/language/index.html).
Notable features used in Syho are:
- [**Sized types**](https://agda.readthedocs.io/en/latest/language/sized-types.html)
- [**Copatterns**](https://agda.readthedocs.io/en/latest/language/copatterns.html)
- [**Record modules**](https://agda.readthedocs.io/en/latest/language/record-types.html#record-modules)
- [**With-abstraction**](https://agda.readthedocs.io/en/latest/language/with-abstraction.html)
- [**Pattern-matching lambda**](https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html#pattern-matching-lambda)

## Agda Mode

For viewing and editing Agda code, you can use
[**Agda mode** for Emacs](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html),
which is also [ported to VS Code](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode).

## Monospace Unicode Fonts

Syho's source code uses a lot of Unicode characters.
To render them beautifully, we recommend you use monospace Unicode fonts that
support these characters, such as the following:
- [**JuliaMono**](https://juliamono.netlify.app/)
    + It has a very large Unicode cover and supports all the Unicode characters
        used in Syho's source code.
- [**Menlo**](https://en.wikipedia.org/wiki/Menlo_(typeface))
    + It is preinstalled in Mac and pretty beautiful. Some characters (e.g., ⊢
        and ⊨) are not supported.

For example, in VS Code, you can use the following setting (in `settings.json`)
to use Menlo as the primary font and fill in some gaps with JuliaMono.
```json
"editor.fontFamily": "Menlo, JuliaMono"
```
