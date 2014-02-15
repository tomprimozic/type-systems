Grow Your Own Type System
=========================


This repository contains implementations of different type systems in OCaml.

It is meant to help out anyone who wants to learn more about advanced type systems and
type inference or experiment by extending or implementing their own. The implementations
are minimal and contain code that is (hopefully) simple and clear.

-   [**algorithm_w**](https://github.com/tomprimozic/type-systems/tree/master/algorithm_w)
    contains one of the most basic, yet efficient implementation of Damas-Hindley-Milner
    type inference algorithm (used in functional languages such as OCaml, Haskell and Elm)
    called *Algorithm W*. Uses references to simulate type substitutions and assigns
    ranks/levels to type variables to simplify let-generalization.

-   [**extensible_rows**](https://github.com/tomprimozic/type-systems/tree/master/extensible_rows)
    extends **algorithm_w** with type inference for extensible records/rows
    with scoped labels, based on Daan Leijen's excellent [paper][extensible_rows]. Although
    this is just one way of implementing extensible records, it's extremly simple and
    surprisingly useful.

-   [**first_class_polymorphism**](https://github.com/tomprimozic/type-systems/tree/master/first_class_polymorphism)
    extends **algorithm_w** with type checking and partial type inference for first-class
    and higher-rank polymorphism, based on another one of Daan Leijen's [papers][hmf].
    This system requires slightly more type annotations than other attempts at type inference for
    first-class polymorphism, such as ML<sup>F</sup>, but is considerably simpler to implement and use.




[extensible_rows]: http://research.microsoft.com/apps/pubs/default.aspx?id=65409
[hmf]: http://research.microsoft.com/apps/pubs/default.aspx?id=132621
