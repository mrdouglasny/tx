import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ENat.Basic

/-!
Lean 4 counterpart of a subset of the invariants provided by the
`graphcalc` Python library.

Currently covered
================

* `chromatic_number`  – smallest number of colours in a proper vertex colouring;
* `clique_number`     – size of a largest clique (maximum clique size);
* `edge_cover_number` – size *or* `⊤` of a smallest edge cover.

> ### About `edge_cover_number`
> Mathlib&nbsp;4 does not yet package an "edge cover number" out of the box, so
> we provide a self‑contained definition below.  It returns an
> `ℕ∞` (extended naturals): the infimum of all finite edge‑cover sizes, or `⊤`
> when no edge cover exists (for example, when the graph has an isolated
> vertex).
>
> This matches the behaviour of `graphcalc.edge_cover_number`, which also
> raises an exception / returns infinity for graphs without an edge cover.
-/

open SimpleGraph
open scoped Classical

universe u

variable {V : Type u}

/-- The **chromatic number** of a graph `G`.

It is the least `n : ℕ∞` such that `G` admits an `n`‑colouring.  This is just
`G.chromaticNumber`, exposed under a snake‑case name to mirror *GraphCalc*’s
API.

If you need a plain `ℕ`, recover it with `ENat.toNat` provided the value is
finite (`≠ ⊤`).
-/
noncomputable def chromatic_number (G : SimpleGraph V) : ℕ∞ :=
  G.chromaticNumber

/-- The **clique number** of `G` – the size of a largest clique.

This is simply `G.cliqueNum` but presented with a snake‑case identifier so
that `clique_number` lines up with *GraphCalc*’s
`graphcalc.clique_number`.
-/
noncomputable def clique_number (G : SimpleGraph V) : ℕ :=
  G.cliqueNum

/-- A predicate saying that a set of edges `C` is an **edge cover** of `G`:
* every edge in `C` is indeed an edge of `G`, *and*
* for every vertex `v`, some edge of `C` is incident to `v`.
-/
@[simp]
def IsEdgeCover (G : SimpleGraph V) (C : Set (Sym2 V)) : Prop :=
  C ⊆ G.edgeSet ∧ ∀ v : V, ∃ e : Sym2 V, (e ∈ C) ∧ v ∈ e

/-- The **edge cover number** of `G`.

It is defined as the infimum (in `ℕ∞`) of the cardinalities of all finite
edge covers.  When `G` possesses no edge cover (e.g. it has an isolated
vertex) the set we take the infimum of is empty, and the value is `⊤` by
convention.

We quantify over *finite* edge sets, hence the `[Fintype V]` requirement so
that the ambient edge set is itself finite.
-/
noncomputable def edge_cover_number (G : SimpleGraph V) [Fintype V] : ℕ∞ := by
  classical
  -- The set of candidate sizes, expressed in `ℕ∞` for convenient `Inf`.
  let S : Set ℕ∞ :=
    {n | ∃ C : Finset (Sym2 V),
        (∀ e, e ∈ C → (e : Sym2 V) ∈ G.edgeSet) ∧          -- every edge belongs to G
        (∀ v : V, ∃ e, e ∈ C ∧ v ∈ e) ∧                    -- cover condition
        n = (C.card : ℕ∞)}                                -- tie size to `n`
  exact sInf S
