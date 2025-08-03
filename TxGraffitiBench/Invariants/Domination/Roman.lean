import TxGraffitiBench.Invariants.Basic

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

-- ROMAN DOMINATION

-- A Roman dominating function on a graph G=(V,E) is a function satisfying the
-- condition that every vertex u for which f(u)=0 is adjacent to at least one
-- vertex v for which f(v)=2.
-- https://www.sciencedirect.com/science/article/pii/S0012365X03004473
def IsRomanDominatingFunction (G : SimpleGraph V) (f : V → Fin 3) : Prop :=
  ∀ v : V, f v = 0 → ∃ w, G.Adj v w ∧ f w = 2

noncomputable def roman_domination_number (G : SimpleGraph V) :=
  let S : Set ℕ :=
    {n | ∃ f : V → Fin 3, (IsRomanDominatingFunction G f) ∧ n = (∑ v, f v)}
  sInf S

-- double roman domination; https://www.sciencedirect.com/science/article/pii/S0166218X1630155X
/--
f(v) = 0 -> 2 neighbors with 2 or 1 neighbor with 3
f(v) = 1 -> at least one neighbor geq 2.
-/
def IsDoubleRomanDominatingFunction (G : SimpleGraph V) (f : V → Fin 4) : Prop :=
  ∀ v : V, (f v = 1 → ∃ w, G.Adj v w ∧ f w ≥ 2)
    ∧ (f v = 0 →
        (∃ w, G.Adj v w ∧ f w = 3) ∨
        (∃ w1 w2 : V, w1 ≠ w2 ∧ G.Adj v w1 ∧ G.Adj v w2 ∧ f w1 = 2 ∧ f w2 = 2))

noncomputable def double_roman_domination_number (G : SimpleGraph V) :=
  let S : Set ℕ :=
    {n | ∃ f : V → Fin 4, (IsDoubleRomanDominatingFunction G f) ∧ n = (∑ v, f v)}
  sInf S
