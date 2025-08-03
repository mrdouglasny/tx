-- K FORCING AND POWER DOMINATION
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph

import TxGraffitiBench.Invariants.Basic

import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Archimedean -- needed for sInf and sSup (set infimum/supremum) on the reals
import Mathlib.Order.OrderIsoNat

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

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

noncomputable def total_zero_forcing_number (G : SimpleGraph V) :=
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsZeroForcingSet G C)
      ∧ (¬ subgraph_has_isolated_vertex (subgraph_from_set G C))
      ∧ n = C.ncard}
  sInf S

-- PSD zero forcing: different color change rule:
-- split G - S into connected components
-- color neighbors if a black vertex has at most one white neighbor in a certain
-- connected component
def PSDForcingStep (k : ℕ) (G : SimpleGraph V) (S : Set V) : Set V :=
  let currWhite : Set V := {v | v ∉ S}  -- white vertices
  let newBlack := ⋃ C : (G.induce currWhite).ConnectedComponent,
    let CsetV : Set V := {x.1 | x ∈ C.supp} -- needed to turn currWhite back into V
    {
        w | ∃ v ∈ S, w ∈ CsetV
            ∧ G.Adj v w ∧
        -- v has exactly one white neighbor in its component
        atMost k {z | G.Adj v z ∧ z ∈ CsetV}
    }
  S ∪ newBlack

inductive PSDForces (k : ℕ) (G : SimpleGraph V) : Set V → Set V → Prop
  | refl  {S} : PSDForces k G S S
  | step  {S T} (hST : PSDForces k G S T) : PSDForces k G S (PSDForcingStep k G T)

def IsPSDForcingSet (k : ℕ) (G : SimpleGraph V) (C : Set V) : Prop :=
  PSDForces k G C ⊤

noncomputable def k_psd_forcing_number (k : ℕ) (G : SimpleGraph V) : ℕ :=
  let S : Set ℕ :=
    {n | ∃ C : Set V, (IsPSDForcingSet k G C) ∧ n = C.ncard}
  sInf S

noncomputable def positive_semidefinite_zero_forcing_number (G : SimpleGraph V) : ℕ :=
  k_psd_forcing_number 1 G
