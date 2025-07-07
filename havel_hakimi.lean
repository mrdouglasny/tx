import Mathlib.Data.List.Sort
import Init.Data.List.Basic

/--
This currently does one step of the havel_hakimi algorithm.
A fully recursive version would have to come with a proof of termination,
which I attempted to complete below in havel_hakimi_full.
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

-- Learning how termination_by works
def sumList (lst : List Nat) : Nat :=
  match lst with
  | []      => 0
  | x :: xs => x + sumList xs
termination_by lst

def test_function (x : List Nat) : List Nat :=
  match x with
  | [] => [12]
  | a :: _ => a :: [12]

-- example from wikipedia
-- #eval havel_hakimi_step [6, 3, 3, 3, 3, 2, 2, 2, 2, 1, 1]
-- #eval havel_hakimi_step [2, 2, 2, 2, 1, 1, 2, 2, 1, 1]
-- #eval havel_hakimi_step [1, 1, 2, 2, 2, 1, 1, 1, 1]

-- #eval havel_hakimi_full [3, 3, 3, 3]

def havel_hakimi_full2 (ds : List Nat) : List Nat :=
  let sorted := ds.insertionSort (· ≥ ·)
  match sorted with
  | [] => []
  | d :: rest =>
    if d == 0 then
      sorted
    else
      let (takeD, dropD) := rest.splitAt d
      if takeD.any (· == 0) then
        sorted
      else
        let newRest := (takeD.map (· - 1)) ++ dropD
        havel_hakimi_full2 newRest
  termination_by ds.length
  decreasing_by sorry
  -- decreasing_by
  --   simp
  --   let sorted := ds.insertionSort (· ≥ ·)
  --   match sorted with
  --   | [] => trivial
  --   | d :: rest =>
  --     split_ifs with h1 h2
  --     let sorted := ds.insertionSort (· ≥ ·)

def havel_hakimi_full (ds : List Nat) : List Nat :=
  match ds.insertionSort (· ≥ ·) with
  | [] => []
  | d :: rest =>
    if d == 0 then
      d :: rest
    else
      let (takeD, dropD) := rest.splitAt d
      if takeD.any (· == 0) then
        d :: rest
      else
        let newRest := (takeD.map (· - 1)) ++ dropD
        havel_hakimi_full newRest
termination_by ds.length
decreasing_by
sorry
