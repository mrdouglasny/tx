import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Archimedean -- needed for sInf and sSup (set infimum/supremum) on the reals
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.List.Basic
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Floor.Div

/-!
Lean 4 counterpart of a subset of the invariants provided by the
`graphcalc` Python library.

Here are the invariants listed at
https://graphcalc.readthedocs.io/en/latest/modules/invariants.html

The ones listed with an x are still in progress.
================

- Traditional Invariants:
  - chromatic_number()
  - clique_number()
  - edge_cover_number()
  - independence_number()
  - matching_number()
  - min_maximal_matching_number()
  - vertex_cover_number()
  - average_degree()
  - degree()
  - degree_sequence()
  - harmonic_index()
  - maximum_degree()
  - minimum_degree()
  - complement_is_connected()
  - well_splitting_number()
- Degree Sequence Based:
  x annihilation_number()
  x residue()
  x slater()
- Domination Number and Friends
  - sub_k_domination_number()
  - sub_total_domination_number()
  - domination_number()
  - independent_domination_number()
  - outer_connected_domination_number()
  - total_domination_number()
- Rainbow Domination and Friends
  x minimum_rainbow_dominating_function()
  x three_rainbow_domination_number()
  x two_rainbow_domination_number()
- Roman Domination and Friends
  x roman_domination_number()
  x double_roman_domination_number()
- Matrix Invariants and Friends
  - adjacency_eigenvalues()
  - adjacency_matrix()
  - algebraic_connectivity()
  - laplacian_eigenvalues()
  - laplacian_matrix()
  - largest_laplacian_eigenvalue()
  - second_largest_adjacency_eigenvalue()
  - smallest_adjacency_eigenvalue()
  - spectral_radius()
  - zero_adjacency_eigenvalues_count()
- Forcing Number/Power Domination
  - connected_zero_forcing_number()
  - k_forcing_number()
  - k_power_domination_number()
  - positive_semidefinite_zero_forcing_number()
  - power_domination_number()
  - total_zero_forcing_number()
  - two_forcing_number()
  - zero_forcing_number()

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
open FiniteDimensional

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

MRD: I think it's OK to use adjMatrix ℝ rather than casting adjacency_matrix.
-/

noncomputable def adjacency_matrix (G: SimpleGraph V) : Matrix V V ℕ :=
  G.adjMatrix ℕ

-- I realized if this returns a Set, there is no multiplicity.
-- This will make counting zero eigenvalues difficult.
noncomputable def adjacency_eigenvalues2 (G : SimpleGraph V) : Set ℝ :=
  let real_adj_matrix : Matrix V V ℝ := (adjacency_matrix G).map (↑)
  spectrum ℝ real_adj_matrix

noncomputable def adjacency_eigenvalues (G : SimpleGraph V) :=
  spectrum ℝ (G.adjMatrix ℝ)

noncomputable def smallest_adjacency_eigenvalue (G : SimpleGraph V) :=
  sInf (adjacency_eigenvalues G)

noncomputable def spectral_radius (G : SimpleGraph V) :=
  sSup ((adjacency_eigenvalues G).image abs)

-- Method 2: number of zero eigenvalues = dimension kernel = n - dim image
noncomputable def zero_adjacency_eigenvalues_count' (G: SimpleGraph V) :=
    Module.rank ℝ (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ)))

-- Method 3: eigenvalues returns an indexable object
noncomputable def adjacency_eigenvalues' (G : SimpleGraph V) := by
  let real_adj_matrix : Matrix V V ℝ := (G.adjMatrix ℝ) -- (adjacency_matrix G).map (↑)
  have hS : Matrix.IsSymm real_adj_matrix := G.isSymm_adjMatrix
  have hA : Matrix.IsHermitian real_adj_matrix := by
    simpa [Matrix.conjTranspose,hS]
  exact hA.eigenvalues

noncomputable def zero_adjacency_eigenvalues_count (G : SimpleGraph V) :=
  Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ)))

noncomputable def algebraic_connectivity (G : SimpleGraph V) : Option ℝ :=
  let eigval_func := adjacency_eigenvalues' G
  let image := Finset.image eigval_func Finset.univ
  let sorted := image.sort (· ≤ ·)
  sorted[1]?

noncomputable def second_largest_adjacency_eigenvalue (G : SimpleGraph V) : Option ℝ :=
  let eigval_func := adjacency_eigenvalues' G
  let image := Finset.image eigval_func Finset.univ
  let sorted := image.sort (· ≥ ·)
  sorted[1]?

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

def IsOuterConnectedDominatingSet (G : SimpleGraph V) (C : Set V) : Prop :=
  have subgraphC := subgraph_from_set G C
  (IsDominatingSet G C) ∧ (complement_is_connected G subgraphC)

noncomputable def outer_connected_domination_number (G : SimpleGraph V) : ℕ := by
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsOuterConnectedDominatingSet G C) ∧ n = C.ncard}
  exact sInf S

-- K FORCING RELATED INVARIANTS

/-- `atMost k T` says the (finite) set `T` has ≤ `k` elements. -/
def atMost (k : ℕ) (T : Set V) : Prop :=
  ∃ hT : T.Finite, hT.toFinset.card ≤ k

/-- One simultaneous “wave’’ of the *k-forcing* rule. -/
def kForcingStep (k : ℕ) (G : SimpleGraph V) (S : Set V) : Set V :=
  S ∪
    { v | ∃ b,                                    -- a blue vertex `b`
        b ∈ S ∧                                  --   already coloured
        atMost k { w | G.Adj b w ∧ w ∉ S } ∧     -- its white neighbourhood is ≤ k
        G.Adj b v ∧ v ∉ S }                      -- and `v` is one of those neighbours

/-!
### Reflexive-transitive closure of the rule
`kForces k G S T` means that starting from coloured set `S`
we can reach *at most* coloured set `T` in finitely many rounds.
-/
inductive kForces (k : ℕ) (G : SimpleGraph V) :
    Set V → Set V → Prop
| refl  {S} : kForces k G S S
| step  {S T} (hST : kForces k G S T) :
    kForces k G S (kForcingStep k G T)

notation S " ⟹[" k ", " G "] " T => kForces k G S T

/-!
`IsKForcingSet k G C` holds when every vertex becomes blue
after finitely many rounds that start from the initial coloured set `C`.
-/
def IsKForcingSet (k : ℕ) (G : SimpleGraph V) (C : Set V) : Prop :=
-- WH: I believe the below line can be simplified, no?
--  ∃ T, (C ⟹[k, G] T) ∧ T = ⊤      -- `⊤ : Set V` is the universe `Set.univ`
  (C ⟹[k, G] ⊤)

/--
'A zero forcing set is a special case of a k-forcing set where k = 1.'
-/
def IsZeroForcingSet : SimpleGraph V → Set V → Prop :=
  IsKForcingSet 1

noncomputable def k_forcing_number (k : ℕ) (G : SimpleGraph V) : ℕ :=
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsKForcingSet k G C) ∧ n = C.ncard}
  sInf S

noncomputable def zero_forcing_number (G : SimpleGraph V) : ℕ :=
  k_forcing_number 1 G

noncomputable def two_forcing_number (G : SimpleGraph V) : ℕ :=
  k_forcing_number 2 G

noncomputable def connected_zero_forcing_number (G : SimpleGraph V) : ℕ :=
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsZeroForcingSet G C)
      ∧ (subgraph_from_set G C).Connected
      ∧ n = C.ncard}
  sInf S

-- Power domination first includes the neighborhood, and then proceeds with k-forcing
def IsKPowerDominatingSet (k : ℕ) (G : SimpleGraph V) (C : Set V) : Prop :=
  let C_with_nbhd := C ∪ {v | ∃ u ∈ C, G.Adj u v}
  C_with_nbhd ⟹[k, G] ⊤

noncomputable def k_power_domination_number (k : ℕ) (G : SimpleGraph V) : ℕ :=
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsKPowerDominatingSet k G C) ∧ n = C.ncard}
  sInf S

noncomputable def power_domination_number (G : SimpleGraph V) : ℕ :=
  k_power_domination_number 1 G

/--
Alternatively, we could build the set from subgraphs.
Upon further reflecting I think this subgrpah version actually fails.
-/
noncomputable def connected_zero_forcing_number2 (G : SimpleGraph V) : ℕ :=
  let S : Set ℕ :=
    {n | ∃ C : G.Subgraph, (IsZeroForcingSet G C.verts)
      ∧ C.Connected
      ∧ n = C.verts.ncard}
  sInf S

def subgraph_has_isolated_vertex {G : SimpleGraph V} (S : G.Subgraph) : Prop :=
  ∃ v, S.neighborSet v = ∅

-- Will refactor/generalize these two later.
def isolate_free (G : SimpleGraph V) : Prop :=
  ¬ (∃ v, G.neighborSet v = ∅)

noncomputable def total_zero_forcing_number (G : SimpleGraph V) (C : Set V) :=
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsZeroForcingSet G C)
      ∧ (¬ subgraph_has_isolated_vertex (subgraph_from_set G C))
      ∧ n = C.ncard}
  sInf S

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

noncomputable def well_splitting_number (G : SimpleGraph V) (C : Set V) :=
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsWellSplittingSet G C)
      ∧ n = C.ncard}
  sInf S

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

noncomputable def sub_k_domination_number (G : SimpleGraph V) (k : ℕ) :=
  have degree_list := degree_sequence G
  have n := Fintype.card V
  let sorted_degrees := degree_list.insertionSort (· ≥ ·)
  -- one way to express \sum_{i = 0}^{t}
  let all_possible_t := {t | (t + (1 / k) * ∑ i ∈ Finset.range (t + 1), sorted_degrees[i]!) ≥ n}
  sInf all_possible_t

noncomputable def sub_total_domination_number (G : SimpleGraph V) :=
  have degree_list := degree_sequence G
  have n := Fintype.card V
  let sorted_degrees := degree_list.insertionSort (· ≥ ·)
  -- one way to express \sum_{i = 0}^{t}
  let all_possible_t := {t | (∑ i ∈ Finset.range (t + 1), sorted_degrees[i]!) ≥ n}
  sInf all_possible_t
