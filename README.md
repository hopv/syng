# Shog

**Shog** is a separation logic with **syntactic higher-order ghost states**.
It supports *higher-order ghost states* (or *impredicative resources*),
whose model is constructed using the *syntax* of the logic itself.

Unlike Iris, Shog is *not step-indexed*.
Thanks to this, Shog has an intuitive model and can much better support
*termination-sensitive* program reasoning.

Shog is mechanized in *Agda*, a modern dependently typed programming language.
