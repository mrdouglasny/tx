-- K FORCING AND POWER DOMINATION
import TxGraffitiBench.Invariants.Basic

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

-- DOMINATION NUMBER AND FRIENDS

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
    {n | ∃ C : Set V, (G.IsIndepSet C) ∧ (IsDominatingSet G C) ∧ n = C.ncard}
  exact sInf S

def IsTotalDominatingSet (G : SimpleGraph V) (C : Set V) : Prop :=
  ∀ v : V, ∃ w ∈ C, G.Adj v w

noncomputable def total_domination_number (G : SimpleGraph V) : ℕ := by
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsTotalDominatingSet G C) ∧ n = C.ncard}
  exact sInf S

def IsOuterConnectedDominatingSet (G : SimpleGraph V) (C : Set V) : Prop :=
  have subgraphC := subgraph_from_set G C
  (IsDominatingSet G C) ∧ (complement_is_connected G subgraphC)

noncomputable def outer_connected_domination_number (G : SimpleGraph V) : ℕ := by
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsOuterConnectedDominatingSet G C) ∧ n = C.ncard}
  exact sInf S

noncomputable def sub_k_domination_number (G : SimpleGraph V) (k : ℕ) :=
  have degree_list := degree_sequence G
  have n := Fintype.card V
  let sorted_degrees := degree_list.insertionSort (· ≥ ·)
  -- one way to express \sum_{i = 0}^{t}
  let all_possible_t := {t | (t + (1 / k) * ∑ i ∈ Finset.range (t + 1), sorted_degrees[i]!) ≥ n}
  sInf all_possible_t

noncomputable def slater (G : SimpleGraph V) :=
  sub_k_domination_number G 1

noncomputable def sub_total_domination_number (G : SimpleGraph V) :=
  have degree_list := degree_sequence G
  have n := Fintype.card V
  let sorted_degrees := degree_list.insertionSort (· ≥ ·)
  -- one way to express \sum_{i = 0}^{t}
  let all_possible_t := {t | (∑ i ∈ Finset.range (t + 1), sorted_degrees[i]!) ≥ n}
  sInf all_possible_t
