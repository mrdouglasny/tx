import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Real.Archimedean -- needed for sInf and sSup (set infimum/supremum) on the reals
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-!
Lean 4 counterpart of a subset of the invariants provided by the
`graphcalc` Python library.

Currently covered
================

* `chromatic_number`  – smallest number of colours in a proper vertex colouring;
* `clique_number`     – size of a largest clique (maximum clique size);
* `edge_cover_number` – size *or* `⊤` of a smallest edge cover.
* `independence_number` - size of largest independent set
* `matching number` - NOT DONE YET
* `vertex cover number` - size of minimum vertex cover
* `annihilation number` - NOT DONE YET
* `average degree` - average of vertex degrees
* `degree` - degree of a given vertex
* `degree sequence` - list all vertex degrees, preserving duplicates
* `harmonic index` - sum of 2 / (deg(u) + deg(v)) over all edges {u, v}
* `maximum degree` - max degree, duh
* `minimum degree` - min degree, duh

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

-- For now, we will only work over finite graphs.
-- DecidableEq V needed for eigenvalues
variable {V : Type u} [Fintype V] [DecidableEq V]

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

noncomputable def independence_number (G : SimpleGraph V) : ℕ :=
  G.indepNum

/--
Take advantage of Mathlib's SimpleGraph.Subgraph.IsMatching function
-/
noncomputable def matching_number (G : SimpleGraph V) :=
  let S : Set ℕ :=
    {n | ∃ C : G.Subgraph, (C.IsMatching) ∧ n = C.verts.ncard}
  sInf S

/--
vertex cover: for each edge (u, v), either u or v is inside the vertex cover
AFAICT, mathlib does not have a built in 'isvertexcover' function.
-/
def IsVertexCover (G : SimpleGraph V) (C : Set V) : Prop :=
  ∀ e ∈ G.edgeSet, ∃ v ∈ e, v ∈ C

-- Set has an ncard method which returns ℕ, as opposed to Set.encard
-- which returns ℕ∞
noncomputable def vertex_cover_number (G : SimpleGraph V) : ℕ := by
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsVertexCover G C) ∧ n = C.ncard}
  exact sInf S

/--
Checks if the complement of a set S in the graph G induces a connected subgraph.

The complement of S is defined as the set of all nodes in G that are not in S.
This function verifies whether the subgraph induced by the complement of S is connected.
-/
noncomputable def complement_is_connected (G : SimpleGraph V) (S : G.Subgraph): Prop :=
  Sᶜ.Connected

noncomputable def degree (G : SimpleGraph V) (v : V) :=
  G.degree v

/--
average_degree

Obviously this is always a rational number. I've made it a real for now,
but we can change it back to a rational in ℚ if needed.
-/
noncomputable def average_degree (G : SimpleGraph V) : ℚ :=
  let total_degree := ∑ v, (G.degree v)
  total_degree / Fintype.card V

/--
degree_sequence: 'the list of vertex degrees in the graph,
optionally sorted in nonincreasing order.'

Because two vertices can have the same degree, we cannot use a Finset here -
Finsets do not allow duplicates. We can either use MultiSet (allows duplicates,
but no order) or List (duplicates and order).

I haven't implemented the 'optional sorting' part yet; how important is that?
-/
noncomputable def degree_sequence (G : SimpleGraph V) : List ℕ :=
-- (Finset.univ : Finset V).val.map (λ v => G.degree v) will return a MultiSet instead
   (Finset.univ : Finset V).toList.map (λ v => G.degree v)

/--
Finset.max returns WithBot ℕ (just the naturals with a ⊥ element) to
account for empty lists. However, I think the graph on no vertices
will have an empty degree list.
-/
noncomputable def maximum_degree (G : SimpleGraph V) : WithBot ℕ :=
   ((Finset.univ : Finset V).image (λ v => G.degree v)).max

noncomputable def minimum_degree (G : SimpleGraph V) : WithBot ℕ :=
   ((Finset.univ : Finset V).image (λ v => G.degree v)).min

/--
If you use this code instead
```
noncomputable def adjacency_matrix (G: SimpleGraph V) :=
  G.adjMatrix ℕ
noncomputable def adjacency_eigenvalues (G : SimpleGraph V) : Set ℝ :=
  spectrum ℝ (adjacency_eigenvalues G))
```
there is this type error:

failed to synthesize
  Algebra ℝ (Matrix V V ℚ)

Thus I manually do the cast.
-/
noncomputable def adjacency_matrix (G: SimpleGraph V) : Matrix V V ℕ :=
  G.adjMatrix ℕ

-- I realized if this returns a Set, there is no multiplicity.
-- This will make counting zero eigenvalues difficult.
noncomputable def adjacency_eigenvalues (G : SimpleGraph V) : Set ℝ :=
  let real_adj_matrix : Matrix V V ℝ := (adjacency_matrix G).map (↑)
  spectrum ℝ real_adj_matrix

noncomputable def smallest_adjacency_eigenvalue (G : SimpleGraph V) :=
  sInf (adjacency_eigenvalues G)

noncomputable def spectral_radius (G : SimpleGraph V) :=
  sSup ((adjacency_eigenvalues G).image abs)

-- Method 2: number of zero eigenvalues = dimension kernel = n - dim image
noncomputable def adjacency_eigenvalues2 (G: SimpleGraph V) :=
    Module.rank ℝ (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ)))

-- Method 3: eigenvalues returns an indexable object
noncomputable def adjacency_eigenvalues3 [DecidableEq V] (G : SimpleGraph V) := by
  let real_adj_matrix : Matrix V V ℝ := (adjacency_matrix G).map (↑)
  have hA : Matrix.IsHermitian real_adj_matrix := by
    sorry
  exact hA.eigenvalues

/--
Because G.degree returns a ℕ, it doesn't suffice to assume
the matrix entries are of type α with [Neg α] [Zero α] [One α]
-/
noncomputable def laplacian_matrix (G : SimpleGraph V): Matrix V V ℤ :=
  Matrix.of fun u v =>
    if u == v then
        G.degree u
    else if G.Adj u v then
        -1
    else
        0

def laplacian_eigenvalues (G : SimpleGraph V) : Set ℝ :=
  let real_lap_matrix : Matrix V V ℝ := (laplacian_matrix G).map (↑)
  spectrum ℝ real_lap_matrix

noncomputable def largest_laplacian_eigenvalue (G : SimpleGraph V) :=
  sSup (laplacian_eigenvalues G)

-- dominating set: each vertex is either in the dominating set or adjacent
-- to a vertex in the set
def IsDominatingSet (G : SimpleGraph V) (C : Set V) : Prop :=
  ∀ v : V, v ∈ C ∨ (∃ w ∈ C, G.Adj v w)

noncomputable def domination_number (G : SimpleGraph V) : ℕ := by
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsDominatingSet G C) ∧ n = C.ncard}
  exact sInf S

noncomputable def independent_domination_number (G : SimpleGraph V) : ℕ := by
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsIndepSet G C) ∧ (IsDominatingSet G C) ∧ n = C.ncard}
  exact sInf S

def IsTotalDominatingSet (G : SimpleGraph V) (C : Set V) : Prop :=
  ∀ v : V, ∃ w ∈ C, G.Adj v w

noncomputable def total_domination_number (G : SimpleGraph V) : ℕ := by
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsTotalDominatingSet G C) ∧ n = C.ncard}
  exact sInf S

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
