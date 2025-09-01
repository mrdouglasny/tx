import TxGraffitiBench.Invariants.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Acyclic

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

open Classical

/--
SHIM DEFINITIONS FOR CONJECTURE USAGE
The output of TxGraffiti2 uses slighly different names which we define as syntactic sugar here.
This allows the output to be effectively directly exportable into Lean.
-/
alias max_degree := maximum_degree
alias min_degree := minimum_degree
def order (_ : SimpleGraph V) := Fintype.card V
noncomputable def size (G : SimpleGraph V) := G.edgeFinset.card
def connected (G : SimpleGraph V) := G.Connected
def bipartite (G : SimpleGraph V) := G.IsBipartite

def tree (G : SimpleGraph V) := G.IsTree
def triangle_free (G : SimpleGraph V) := G.CliqueFree 3

def has_claw (G : SimpleGraph V) :=
  ∃ (a b c d : V), G.Adj a b ∧ G.Adj a c ∧ G.Adj a d
  ∧ (¬G.Adj b c) ∧ (¬G.Adj b d) ∧ (¬G.Adj c d)

def claw_free (G : SimpleGraph V) :=
  ¬ has_claw G
