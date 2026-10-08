import GameTheory.Math.GridCrossingPlacement

/-! A grid point determines its unique spacing-three switch box. Its row and
column then identify the two possible wire owners using arithmetic and a
constant number of original pointer queries, without enumerating graph edges. -/

namespace GameTheory.Math.GridCrossing

open GameTheory.Math.GridWire GameTheory.Math.EndOfLine

/-- The nearest spacing-three center, with ties resolved by the grid partition. -/
def crossingCenter (p : ℕ × ℕ) : ℕ × ℕ :=
  (3 * ((p.1 + 1) / 3), 3 * ((p.2 + 1) / 3))

theorem crossingCenter_coordinates (p : ℕ × ℕ) :
    (crossingCenter p).1 % 3 = 0 ∧ (crossingCenter p).2 % 3 = 0 := by
  simp [crossingCenter]

theorem crossingCenter_neighborhood (p : ℕ × ℕ) :
    crossingNeighborhood (crossingCenter p) p := by
  unfold crossingCenter crossingNeighborhood
  dsimp only
  omega

/-- A spacing-three switch box is recovered from any of its grid points. -/
theorem crossingCenter_eq {center p : ℕ × ℕ}
    (hc : center.1 % 3 = 0 ∧ center.2 % 3 = 0)
    (hp : crossingNeighborhood center p) : crossingCenter p = center := by
  by_contra h
  exact crossingNeighborhood_disjoint (crossingCenter_coordinates p) hc h
    (crossingCenter_neighborhood p) hp

/-- Outgoing rows identify the source directly; incoming rows query its predecessor. -/
def horizontalOwner (P : ℕ → ℕ) (center : ℕ × ℕ) : ℕ :=
  if center.2 % 6 = 0 then center.2 / 6 else P (center.2 / 6)

/-- The source label is the high field of the allocated column. -/
def verticalOwner (n : ℕ) (center : ℕ × ℕ) : ℕ := (center.1 / 3) / n

theorem horizontalOwner_eq {n i : ℕ} {P S : ℕ → ℕ} {center : ℕ × ℕ}
    (ha : HasSuccessor P S i) (hh : horizontalInterior n i (S i) center) :
    horizontalOwner P center = i := by
  rcases hh with ⟨_, _, hy | hy⟩
  · simp [horizontalOwner, hy]
  · have hd : (6 * S i + 3) / 6 = S i := by omega
    simp [horizontalOwner, hy, hd, ha.2]

theorem verticalOwner_eq {n i : ℕ} {S : ℕ → ℕ} {center : ℕ × ℕ}
    (hs : S i < n) (hv : verticalInterior n i (S i) center) :
    verticalOwner n center = i := by
  have hn : 0 < n := by omega
  simp [verticalOwner, hv.1, wireColumn, Nat.mul_add_div hn, Nat.div_eq_of_lt hs]

/-- Identify and validate the horizontal and vertical owners of a proper crossing. -/
def crossingOwners (n : ℕ) (P S : ℕ → ℕ) (center : ℕ × ℕ) : Option (ℕ × ℕ) :=
  let i := horizontalOwner P center
  let k := verticalOwner n center
  if i < n ∧ k < n ∧ S i < n ∧ S k < n ∧ i ≠ k ∧
      HasSuccessor P S i ∧ HasSuccessor P S k ∧
      horizontalInterior n i (S i) center ∧ verticalInterior n k (S k) center then
    some (i, k)
  else none

/-- Every genuine crossing is recovered exactly by the local query. -/
theorem crossingOwners_complete {n i k : ℕ} {P S : ℕ → ℕ} {center : ℕ × ℕ}
    (hi : i < n) (hk : k < n) (hsi : S i < n) (hsk : S k < n) (hne : i ≠ k)
    (hai : HasSuccessor P S i) (hak : HasSuccessor P S k)
    (hh : horizontalInterior n i (S i) center) (hv : verticalInterior n k (S k) center) :
    crossingOwners n P S center = some (i, k) := by
  simp [crossingOwners, horizontalOwner_eq hai hh, verticalOwner_eq hsk hv,
    hi, hk, hsi, hsk, hne, hai, hak, hh, hv]

/-- A successful query certifies both bounded consistent edges and their crossing geometry. -/
theorem crossingOwners_sound {n i k : ℕ} {P S : ℕ → ℕ} {center : ℕ × ℕ}
    (h : crossingOwners n P S center = some (i, k)) :
    i < n ∧ k < n ∧ S i < n ∧ S k < n ∧ i ≠ k ∧
      HasSuccessor P S i ∧ HasSuccessor P S k ∧
      horizontalInterior n i (S i) center ∧ verticalInterior n k (S k) center := by
  dsimp only [crossingOwners] at h
  split_ifs at h with hc
  · cases Option.some.inj h
    exact hc

end GameTheory.Math.GridCrossing
