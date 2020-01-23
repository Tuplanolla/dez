Do these things.

* Imagine a hub, where roosters, camels and sea thrifts grow.
* Set up build automation, such that we
    * build Coq files in `theories`,
    * build Coq files and extract OCaml files in `oasis-hub`,
    * build Thrift files and extract OCaml files in `oasis-hub`,
    * build extracted OCaml files in `oasis-hub`,
    * build C++ files in `gfd`,
    * build Thrift files and extract C++ files in `gfd-spoke`,
    * build extracted C++ files in `gfd-spoke`,
* Add adverb subdirectories to arrange different conceps with similar names.
* Implement `Is/Algebraically/Group.v` and `Is/Algebraically/Associative.v`.
* Integrate Thrift into the mess.
* Monoidal categories now.

Some rules.

* Abbreviate
    * Coq has: refl, sym, trans, assoc, comm, involutive, distr,
      l (left), r (right), inj (injective)
    * Coq reserves: fun, unit
    * Categorical literature has: Mon, Grp, Top, op
* Import
    * Coq has: refl, sym, trans, assoc, comm, distr,
      l (left), r (right), inj (injective)
    * Maniunfold has: fn, un, invol, absorb

Wikipedia educates.

* f : Q × R → S (binary function)
    Example: exponentiation
    Example: set membership
    Examples: matrix multiplication, the tensor product, and the Cartesian product
* f : R × R → S (internal binary function)
    Example: internal binary relations
    Examples: the dot product, the inner product, and metrics
* f : R × S → S (external binary operation)
    Examples: dynamical system flows, group actions, projection maps, and scalar multiplication
* f : S × S → S (binary operation)
    Examples: addition, multiplication, permutations, and the cross product

Every binary operation is

* external binary operation
* internal binary function

and everyone of these is

* binary function,

forming a diamond.

Solve this equation

```
    E
---------
  D
-----
A + B * C
    -----
      F
---------
    G
```

to get

```
(+) : A * B -> B
(*) : B * C -> B
```

as the most general type for biassociativity.
The operations unify to get

```
(+) : A * A -> A
(*) : A * A -> A
```

as the most general type for associativity.

Solve this equation

```
    C
---------
  B
-----
(- x) + x
  ---  ---
   A    A
```

to get

```
(-) : A -> B
(+) : B * A -> C
```

as the most general type for bileftinvertibility.

```
% This is the first known publication of the broker pattern.
% Surprisingly, the broker revisited pattern by the same authors ruin it all.

@book{buschmann-1996,
  author = {Frank Buschmann and Regine Meunier and Hans Rohnert and
    Peter Sommerlad and Michael Stal},
  title = {Pattern-Oriented Software Architecture},
  subtitle = {A System of Patterns},
  chapter = {Architectural Patterns / Distributed Systems / Broker},
  date = {1996},
  edition = {1},
  volume = {1},
  pages = {99--122},
  publisher = {John Wiley \& Sons},
}
```
