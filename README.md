# Shog

**Shog** is a separation logic with **syntactic higher-order ghost states**.
It supports *higher-order ghost states* (or *impredicative resources*),
whose model is constructed using the *syntax* of the logic itself.

Unlike Iris, Shog is *not step-indexed*.
Thanks to this, Shog has an intuitive model and can much better support
*termination-sensitive* program reasoning.

Shog is mechanized in *Agda*, a modern dependently typed programming language.

## Installation

1. [Install Agda 2.6.*](https://agda.readthedocs.io/en/latest/getting-started/installation.html).
2. [Install Agda standard library 1.7.*](https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md).

We have checked that Shog works at least with
[Agda](https://github.com/agda/agda) 2.6.2.2
and [Agda standard library](https://github.com/agda/agda-stdlib) 1.7.1.

For viewing and editing Agda code, we recommend
[Agda mode for Emacs](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
and [Agda mode for VS Code](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode).
