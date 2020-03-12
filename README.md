# ML Type Inference

* [main.pl](./main.pl) implements the classic ML-style type inference (simply typed lambda-calculus + let polymorphism) with some extra features (sum types, product types, fix, booleans, integers, lists). Most of the typing rules are taken from Benjamin Pierce's _Types and Programming Languages_.
* [rec.pl](./rec.pl) implements STLC with recursive types, it exploits the unification algorithm in [SWI Prolog](https://www.swi-prolog.org/), which supports unifying cyclic terms. As a result, this code might not work with other Prolog implementation.
* [synthesis.pl](./synthesis.pl) tries to use the same typing rules (STLC, sum types, product types) for term synthesis, however, due to the inherent depth-first search in Prolog, it doesn't work very well...
