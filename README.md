Grow Your Own Type System
=========================


This repository contains implementations of different type systems in OCaml.

It is meant to help out anyone who wants to learn more about advanced type systems and
type inference or experiment by extending or implementing their own. The implementations
are minimal and contain code that is (hopefully) simple and clear.

-   **algorithm_w**
    Contains the one of the most basic, yet efficient implementation of Damas-Hindley-Milner
		type inference (used in functional languages such as OCaml, Haskell and Elm) algorithm
		called *Algorithm W*. Uses references to simulate type substitutions and assigns
		ranks/levels to type variables to simplify let-generalization.
