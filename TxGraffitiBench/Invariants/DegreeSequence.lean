import TxGraffitiBench.Invariants.Basic
import TxGraffitiBench.Invariants.HavelHakimi

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

/--
The residue of a graph is defined as the number of zeros obtained at the end of the
Havel-Hakimi process. This process determines whether a given degree sequence corresponds
to a graphical sequence, which is a sequence of integers that can be realized as the
degree sequence of a simple graph.
-/
def residue_seq (ds : List ℕ) : ℕ :=
  let end_proc := havel_hakimi_full ds
  end_proc.count 0

/--
The residue of a graph is just the residue_seq of its degree sequence.
-/
noncomputable def residue (G : SimpleGraph V) :=
  let ds := degree_sequence G
  residue_seq ds
