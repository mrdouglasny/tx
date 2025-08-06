import Mathlib.Data.List.Sort
import Init.Data.List.Basic

/--
One step of the havel_hakimi algorithm.
-/
def havel_hakimi_step (ds : List Nat) : List Nat :=
  let ds := ds.insertionSort (· ≥ ·)
  match ds with
  | [] => []
  | d :: rest =>
    -- if d is zero, the previous sorting step means everything is zero,
    -- so sequence is graphical
    -- if d is less than zero, then we're in trouble. but we want to abort the MOMENT
    -- a negative number appears.
    if d == 0 then
      -- Previous sorting step means everything is zero - STOP!
      ds
    else
      -- grab the next d elements
      let (takeD, dropD) := rest.splitAt d
      -- if any are zero, then we would create a negative number - STOP!
      if takeD.any (· == 0) then
        ds
      else
        let newRest := (takeD.map (· - 1)) ++ dropD
        newRest

#eval havel_hakimi_step [1, 1, 1, 1, 1, 1, 1, 1]

/--
The full Havel-Hakimi algorithm
-/
def havel_hakimi_full (ds : List Nat) : List Nat :=
  let sorted := ds.insertionSort (· ≥ ·)
  match hdr : sorted with
  | [] => []
  | d :: rest =>
    if d == 0 then
      sorted
    else
      let split := rest.splitAt d
      let takeD := split.1
      let dropD := split.2
      if takeD.any (· == 0) then
        sorted
      else
        let newRest := (takeD.map (· - 1)) ++ dropD
        havel_hakimi_full newRest
  termination_by ds.length
  decreasing_by
    simp
    have hsd : sorted.length = ds.length := by
      unfold sorted
      apply List.length_insertionSort (· ≥ ·)
    have hr : rest.length < sorted.length := by
      rw [hdr]
      rw [List.length_cons]
      omega
    have h₁ : min d rest.length ≤ d := Nat.min_le_left d rest.length
    have h₁' : min d rest.length ≤ rest.length := Nat.min_le_right d rest.length
    have h₂ : min d rest.length + (rest.length - d) ≤ d + (rest.length - d) :=
      Nat.add_le_add_right h₁ (rest.length - d)
    -- casework on whether d ≤ rest.length
    by_cases h_d_le : d ≤ rest.length
    · have h₃ : d + (rest.length - d) = rest.length := Nat.add_sub_cancel' h_d_le
      rw [h₃] at h₂
      have h₄ : min d rest.length + (rest.length - d) ≤ rest.length := h₂
      rw [←hsd]
      apply lt_of_le_of_lt h₄ hr
    · have hr0 : rest.length - d = 0 := by
        rw [Nat.sub_eq_zero_of_le]
        omega
      rw [←hsd]
      rw [hr0] at h₂
      rw [hr0]
      rw [Nat.add_zero]
      apply lt_of_le_of_lt h₁'
      apply hr

-- example from wikipedia
-- #eval havel_hakimi_step [6, 3, 3, 3, 3, 2, 2, 2, 2, 1, 1]
-- #eval havel_hakimi_step [2, 2, 2, 2, 1, 1, 2, 2, 1, 1]
-- #eval havel_hakimi_step [1, 1, 2, 2, 2, 1, 1, 1, 1]
-- #eval havel_hakimi_full [3, 3, 3, 3]
