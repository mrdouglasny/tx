import TxGraffitiBench.Invariants.Basic

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

-- RAINBOW DOMINATION

-- For a graph G, a set C is a rainbow dominating set for the coloring f:
-- A rainbow dominating set is a set of nodes
-- such that every uncolored node is adjacent to nodes of all k different colors.
def IsRainbowDominatingSet {α : Type _} (G : SimpleGraph V) (C : Set V) (f : V → α) : Prop :=
  ∀ v : V, v ∈ C ∨
    ∃ (N : Set V), -- N is set of neighbors in C
      (∀ u ∈ N, G.Adj v u ∧ u ∈ C) ∧
      -- neighbors' colors cover the entire color space
      (Set.univ : Set α) = f '' N

noncomputable def k_rainbow_domination_number (k : ℕ) (G : SimpleGraph V) : ℕ :=
  let S : Set ℕ :=
    {n | ∃ C : Set V, (∃ f : V → (Fin k), IsRainbowDominatingSet G C f) ∧ n = C.ncard}
  sInf S

noncomputable def two_rainbow_domination_number (G : SimpleGraph V) : ℕ :=
  k_rainbow_domination_number 2 G

noncomputable def three_rainbow_domination_number (G : SimpleGraph V) : ℕ :=
  k_rainbow_domination_number 3 G
