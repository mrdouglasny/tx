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
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Archimedean -- needed for sInf and sSup (set infimum/supremum) on the reals
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Tx.Edge

/-!
Tests of the graph invariants.
-/

open SimpleGraph
open scoped Classical

universe u

-- For now, we will only work over finite graphs.
-- DecidableEq V needed for eigenvalues
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Path graph on `Fin n`: vertices are `0‥n-1`, edges if the indices differ by `1`. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel
     (fun i j => (i.val + 1 = j.val) ∨ (j.val + 1 = i.val))

/-- Cycle graph on `Fin n` (`n ≥ 3`) -/
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel
    (fun i j =>
      (i + 1) % n = j ∨ (j + 1) % n = i)

def K1 := SimpleGraph.completeGraph (Fin 1)
def K2 := SimpleGraph.completeGraph (Fin 2)
def K3 := SimpleGraph.completeGraph (Fin 3)

def A3 := pathGraph 3
def A4 := pathGraph 4
def A5 := pathGraph 5

#check A5.edgeSet.ncard

def C4 := cycleGraph 4

/- Now what we want is to compute all of the invariants using GraphCalc,
   make computable Lean definitions and compare (!?!)
-/
