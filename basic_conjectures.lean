import Tx.Edge
import Mathlib.Combinatorics.SimpleGraph.Acyclic
-- import Hammer (will play around with this more)

-- paper proof of ((¬(Kn)) ∧ (connected) ∧ (isolate_free)) → (independence_number ≥ 2)
-- Any noncomplete simplegraph with no isolated vertices
-- must have two non-adjacent vertices
-- DecidableEq V is needed to explicitly construct Finsets with brace notation
-- like let s : Finset V := {v, w}
-- I use Finsets since the definition of IndepNum uses it.
theorem conjecture_44 {V : Type u} [DecidableEq V] [Fintype V]
                      (G : SimpleGraph V)
                      (hK : G ≠ ⊤)
                      (hC : G.Connected)
                      (hI : isolate_free G) : independence_number G ≥ 2 := by
  have twv : ∃ v w, v ≠ w ∧ ¬ (G.Adj v w) := by
    contrapose! hK with contra_goal
    ext v w
    by_cases h' : v = w
    · simp [h']
    · exact (iff_true_right h').mpr (contra_goal v w h')
  obtain ⟨v, w, hne, hnot⟩ := twv
  let s : Finset V := {v, w}
  have h_indep : G.IsIndepSet s := by
    rw [SimpleGraph.IsIndepSet]
    sorry
  have s_gle_2 : 2 ≤ s.card := by
    rw [Finset.card_pair hne]
  apply le_csSup
  · -- The set of independent set sizes is bounded above by the entire graph
    use Fintype.card V
    rintro n ⟨s, hs_indep, rfl⟩
    exact Finset.card_le_univ s
  · -- 2 is in that set
    use s
    exact ⟨h_indep, by rw [Finset.card_pair hne]⟩
