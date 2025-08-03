/-
Copyright (c) 2025 MRD. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Matching

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Order.Floor.Div -- needed for ceiling division

open SimpleGraph
open Classical

universe u

-- For now, we will only work over finite graphs.
-- DecidableEq V needed for eigenvalues
variable {V : Type u} [Fintype V] [DecidableEq V]

-- SIMPLE INVARIANTS
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
Take advantage of Mathlib's SimpleGraph.Subgraph.IsMatching function.

Maximum Matchings:
The size of a maximum matching is the number of edges.
The matching number is the size of the largest maximum matching.
-/
noncomputable def matching_number (G : SimpleGraph V) :=
  let S : Set ℕ :=
    {n | ∃ C : G.Subgraph, (C.IsMatching) ∧ n = C.edgeSet.ncard}
  sSup S

/--
Maximal Matchings
-/
def IsMaximalMatching (G : SimpleGraph V) (C : G.Subgraph) :=
  C.IsMatching ∧ (¬ ∃ D : G.Subgraph, (D.IsMatching) ∧ C ≤ D)

noncomputable def min_maximal_matching_number (G : SimpleGraph V) :=
  let S : Set ℕ :=
    {n | ∃ C : G.Subgraph, (IsMaximalMatching G C) ∧ n = C.edgeSet.ncard}
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
From GraphCalc:
Compute the well-splitting number S_w(G) of the graph G.
The well-splitting number of a graph is the minimum size of a well-splitting set,
defined as a set S of vertices such that every connected component of G-S has at most
ceil((|V(G)| - |S|) / 2) vertices. A well-splitting set is a set of vertices whose
removal results in a graph where every connected component has a size that is at
most half of the remaining vertices.
-/
def IsWellSplittingSet (G : SimpleGraph V) (C : Set V) : Prop :=
  let gminusc := {v | v ∉ C}
  let gmg := G.induce gminusc
  let bound := (gminusc.ncard) ⌈/⌉ 2 -- 'ceildiv'
  ∀ (conn_comp : (gmg).ConnectedComponent), conn_comp.supp.ncard <= bound

noncomputable def well_splitting_number (G : SimpleGraph V) :=
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsWellSplittingSet G C)
      ∧ n = C.ncard}
  sInf S

-- Create the subgraph on these vertices
def subgraph_from_set (G : SimpleGraph V) (C : Set V) : G.Subgraph :=
  {
    verts := C
    Adj := λ v w ↦ G.Adj v w ∧ v ∈ C ∧ w ∈ C
    adj_sub := λ hadj ↦ hadj.1
    edge_vert := λ hadj ↦ hadj.2.1
    symm := by
      rintro v w ⟨hvw, hv, hw⟩
      exact ⟨G.symm hvw, hw, hv⟩
  }
