import TxGraffitiBench.Invariants.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/--
SHIM DEFINITIONS FOR CONJECTURE USAGE
The output of TxGraffiti2 uses slighly different names which we define as syntactic sugar here.
This allows the output to be effectively directly exportable into Lean.
-/
alias max_degree := maximum_degree
alias min_degree := minimum_degree
def order (_ : SimpleGraph V) := Fintype.card V
def connected (G : SimpleGraph V) := G.Connected
def bipartite (G : SimpleGraph V) := G.IsBipartite
