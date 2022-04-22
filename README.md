# Shog

**Shog** is a separation logic with **syntactic higher-order ghost states**.
It supports *higher-order ghost states* (or *impredicative resources*),
whose model is constructed using the *syntax* of the logic itself.

Unlike Iris, Shog is *not step-indexed*.
Thanks to this, Shog has an intuitive model and can much better support
*termination-sensitive* program reasoning.

Shog is mechanized in *Agda*, a modern dependently typed programming language.

## Installation

1. [Install Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html).
2. [Install Agda standard library](https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md).

We have checked that Shog works with
[Agda](https://github.com/agda/agda) 2.6.2.2
and [Agda standard library](https://github.com/agda/agda-stdlib) 1.7.1.

## Recommended Environment

For viewing and editing Agda code, we recommend
[Agda mode for Emacs](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
and [Agda mode for VS Code](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode).

### Font

The source code uses a lot of Unicode characters, so we recommend you to use
a font that covers these characters.
To render them, you can use any of the following:
- [**Source Code Pro**](https://github.com/adobe-fonts/source-code-pro)
  (Good readability)
- [**DejaVu Sans Mono**](https://dejavu-fonts.github.io/)
  (Very large Unicode cover)
- [**Menlo**](https://en.wikipedia.org/wiki/Menlo_(typeface))
  (Preinstalled in Mac; Very large Unicode cover)

Also, some operators like `|=>` renders nicely with ligatures.
To use ligatures, we recommend [**Fira Code**](https://github.com/tonsky/FiraCode).
Make sure that ligatures are supported.

For example, in VS Code, you can use the following setting (in `settings.json`)
to use ligatures from Fira Code and render unicode letters by Source Code Pro
and DejaVu Sans Mono.
```json
"editor.fontFamily": "Fira Code, Source Code Pro, DejaVu Sans Mono",
"editor.fontLigatures": true,
```
