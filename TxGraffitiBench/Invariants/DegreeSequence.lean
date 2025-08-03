import TxGraffitiBench.Invariants.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Basic
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

open SimpleGraph
open scoped Classical

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

-- DEGREE SEQUENCE BASED

noncomputable def annihilation_number (G : SimpleGraph V) :=
  have degree_list := degree_sequence G
  have m := G.edgeFinset.card
  let sorted_degrees := degree_list.insertionSort (· ≤ ·)
  let all_possible_t := {t | (∑ i ∈ Finset.range (t), sorted_degrees[i]!) ≥ m}
  sSup all_possible_t
