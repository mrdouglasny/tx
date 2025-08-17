# TxGraffitiBench

This repository contains Lean code for TxGraffitiBench, a benchmark and the associated Lean library for formalizations of graph theory invariants. These are a subset of the graph theory invariants provided by the [GraphCalc](https://pypi.org/project/graphcalc/) Python library.

# Invariants
The supported invariants are listed at
https://graphcalc.readthedocs.io/en/latest/modules/invariants.html

# Repository Layout
The Lean files and invariant definitions are stored in `TxGraffitiBench/Invariants` in the following way:
- `Basic.lean`: basic definitions and invariants (e.g. clique number, independence number)
- `Matrix.lean`: matrix-related invariants (e.g. adjacency matrix, spectrum)
- `DegreeSequence.lean`: degree-sequence related invariants
- `HavelHakimi.lean`: implementation and proof of the Havel-Hakimi algorithm
- `Sugar.lean`: compatibility aliases and syntactic sugar (e.g. min_degree as an alias for minimum_degree)
- `Domination/Basic.lean`: simple domination number invariants
- `Domination/Power.lean`: power domination and k-forcing invariants
- `Domination/Rainbow.lean`: rainbow domination invariants
- `Domination/Roman.lean`: roman domination invariants

There is also a file `Imports.lean` for ease of importing everything if you so desire.

# Examples
To use the Lean library, the easiest way is to 
- First add the following lines to `lakefile.lean` in your project to list TxGraffitiBench as a dependency.
    ```
    require TxGraffitiBench from git
    "https://github.com/mrdouglasny/tx"
    ```
- Download the library with
    ```
    lake update
    ```
    in your terminal.
- Then, in files that use the invariant definitions, add
    ```{lean}
    import TxGraffitiBench.Imports
    ```
    at the top of your file.