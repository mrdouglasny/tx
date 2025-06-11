/-
Copyright (c) 2025 MRD. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Antichain
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Invariants for TxGraffiti

Some are already defined and we rename them here.
-/

open Fintype Function

universe u v

open SimpleGraph Coloring

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}

noncomputable def chromatic_number : ℕ∞ := G.chromaticNumber

noncomputable def clique_number : ℕ := G.cliqueNum
