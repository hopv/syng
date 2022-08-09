# Syho

**Syho** is a **syntactically higher-order** separation logic.
It supports *higher-order ghost states* (or *impredicative resources*),
whose semantics is constructed using the *syntax* of the logic itself.

Unlike Iris, Syho is *not step-indexed*.
Thanks to this, Syho has intuitive semantics and can flexibly support
*termination-sensitive* program reasoning.

Syho is mechanized in [**Agda**](https://agda.readthedocs.io/en/latest/),
a modern dependently typed programming language.

## Installation

1. [Install Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html).

That's all!

We have checked that Syho works with Agda 2.6.2.2.

## Learning Agda

You can learn Agda's language features
by [the official document](https://agda.readthedocs.io/en/latest/language/index.html).
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

## Font

The source code uses a lot of Unicode characters, so we recommend you use
a font that covers these characters.
To render them, you can use any of the following:
- [**Source Code Pro**](https://github.com/adobe-fonts/source-code-pro)
  (Good readability)
- [**DejaVu Sans Mono**](https://dejavu-fonts.github.io/)
  (Very large Unicode cover)
- [**Menlo**](https://en.wikipedia.org/wiki/Menlo_(typeface))
  (Preinstalled in Mac; Very large Unicode cover)

Also, some operators like `|=>` render nicely with ligatures.
To use ligatures, we recommend [**Fira Code**](https://github.com/tonsky/FiraCode).
Make sure that ligatures are supported in your editor.

For example, in VS Code, you can use the following setting (in `settings.json`)
to use ligatures from Fira Code and render Unicode letters by Source Code Pro
and DejaVu Sans Mono.
```json
"editor.fontFamily": "Fira Code, Source Code Pro, DejaVu Sans Mono",
"editor.fontLigatures": true,
```
