Do these things.

* Add adverb subdirectories to arrange different conceps with similar names.
* Implement `Is/Algebraically/Group.v` and `Is/Algebraically/Associative.v`.
* Why is `Associative` specialized (to help rewriting), but `Reflexive` is not?
* Organize modules coherently.
* Set up a build system (perhaps Dune).
* Integrate Thrift into the mess.
* Monoidal categories now.

Some rules.

* Abbreviate
    * Coq has: refl, sym, trans, assoc, comm, involutive, l (left), r (right)
    * Coq reserves: fun, unit
    * Categorical literature has: Mon, Grp, Top, op
* Import
    * Coq has refl, sym, trans, assoc, comm, involutive

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
