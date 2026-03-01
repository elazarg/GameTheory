import Mathlib
import Fixpoint.GridSimplex

set_option autoImplicit false

namespace Fixpoint

open scoped BigOperators

namespace KuhnSubdivision

/-- Canonical finite simplex index type of dimension `n`. -/
abbrev Idx (n : ℕ) := Fin (n + 1)

/-- Integer grid vertices for the `n`-simplex with denominator `m`. -/
abbrev GridVertex (n m : ℕ) : Type := GridPoint (Idx n) m

/-- Normalized embedding of a grid vertex into the real standard simplex. -/
noncomputable def toPoint {n m : ℕ} (hm : 0 < m) :
    GridVertex n m → stdSimplex ℝ (Idx n) :=
  GridPoint.toStdSimplex (ι := Idx n) hm

/-- Coordinatewise mesh condition (`<= 1`) between grid vertices. -/
def CoordDiffLeOne {n m : ℕ} (p q : GridVertex n m) : Prop :=
  ∀ i : Idx n, |((p.1 i : ℝ) - (q.1 i : ℝ))| ≤ 1

/-- Under coordinate mesh bound `<= 1`, normalized vertices are at distance `<= 1/m`. -/
theorem dist_toPoint_le_inv_of_coordDiffLeOne
    {n m : ℕ} (hm : 0 < m) (p q : GridVertex n m)
    (hmesh : CoordDiffLeOne p q) :
    dist (toPoint hm p) (toPoint hm q) ≤ (1 : ℝ) / m := by
  have hmRpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcoord : ∀ i : Idx n,
      dist ((toPoint hm p : Idx n → ℝ) i) ((toPoint hm q : Idx n → ℝ) i) ≤ (1 : ℝ) / m := by
    intro i
    have hmesh_i : |((p.1 i : ℝ) - (q.1 i : ℝ))| ≤ 1 := hmesh i
    have hdiv : |((p.1 i : ℝ) - (q.1 i : ℝ))| / m ≤ 1 / m :=
      div_le_div_of_nonneg_right hmesh_i (le_of_lt hmRpos)
    calc
      dist ((toPoint hm p : Idx n → ℝ) i) ((toPoint hm q : Idx n → ℝ) i)
          = |((p.1 i : ℝ) / m) - ((q.1 i : ℝ) / m)| := by
              simp [toPoint, GridPoint.toStdSimplex_apply, Real.dist_eq]
      _ = |((p.1 i : ℝ) - (q.1 i : ℝ)) / m| := by ring_nf
      _ = |((p.1 i : ℝ) - (q.1 i : ℝ))| / m := by
            rw [abs_div, abs_of_pos hmRpos]
      _ ≤ 1 / m := hdiv
  have hnonneg : 0 ≤ (1 : ℝ) / m := by positivity
  simpa [Subtype.dist_eq] using (dist_pi_le_iff hnonneg).2 hcoord

section GridMoves

variable {n m : ℕ}

/-- Increment one coordinate; this moves from denominator-sum `m` to `m + 1`. -/
def incrementCoord (p : GridVertex n m) (i : Idx n) : GridVertex n (m + 1) := by
  refine ⟨(fun k => if k = i then p.1 k + 1 else p.1 k), ?_⟩
  classical
  calc
    ∑ k : Idx n, (if k = i then p.1 k + 1 else p.1 k)
        = ∑ k : Idx n, ((if k = i then (1 : ℕ) else 0) + p.1 k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            by_cases hki : k = i <;> simp [hki, Nat.add_comm]
    _ = (∑ k : Idx n, (if k = i then (1 : ℕ) else 0)) + ∑ k : Idx n, p.1 k := by
          rw [Finset.sum_add_distrib]
    _ = 1 + ∑ k : Idx n, p.1 k := by simp
    _ = m + 1 := by simp [p.2, Nat.add_comm]

@[simp] theorem incrementCoord_apply_same (p : GridVertex n m) (i : Idx n) :
    (incrementCoord p i).1 i = p.1 i + 1 := by
  classical
  simp [incrementCoord]

@[simp] theorem incrementCoord_apply_other (p : GridVertex n m) (i k : Idx n) (hk : k ≠ i) :
    (incrementCoord p i).1 k = p.1 k := by
  classical
  simp [incrementCoord, hk]

/-- Incrementing one coordinate changes each raw integer coordinate by at most one. -/
theorem abs_sub_le_one_incrementCoord (p : GridVertex n m) (i : Idx n) :
    ∀ k : Idx n, |((incrementCoord p i).1 k : ℝ) - (p.1 k : ℝ)| ≤ 1 := by
  intro k
  by_cases hki : k = i
  · subst hki
    rw [incrementCoord_apply_same]
    norm_num
  · rw [incrementCoord_apply_other _ _ _ hki]
    simp

/-- Decrement one coordinate; this moves from denominator-sum `m + 1` to `m`. -/
def decrementCoord (p : GridVertex n (m + 1)) (i : Idx n) (hi : 0 < p.1 i) : GridVertex n m := by
  refine ⟨(fun k => if k = i then p.1 k - 1 else p.1 k), ?_⟩
  classical
  have hiU : i ∈ (Finset.univ : Finset (Idx n)) := by simp
  have hgei : 1 ≤ p.1 i := Nat.succ_le_iff.mpr hi
  have hsplit0 :
      Finset.sum ((Finset.univ : Finset (Idx n)).erase i)
        (fun k : Idx n => if k = i then p.1 k - 1 else p.1 k)
        + (if i = i then p.1 i - 1 else p.1 i)
        = Finset.sum (Finset.univ : Finset (Idx n))
            (fun k : Idx n => if k = i then p.1 k - 1 else p.1 k) := by
    simpa using
      (Finset.sum_erase_add (s := (Finset.univ : Finset (Idx n)))
        (a := i) (f := fun k : Idx n => if k = i then p.1 k - 1 else p.1 k) hiU)
  have hsplit :
      (∑ k : Idx n, (if k = i then p.1 k - 1 else p.1 k))
        = (p.1 i - 1) + Finset.sum ((Finset.univ : Finset (Idx n)).erase i) (fun k => p.1 k) := by
    have hsplit0' := hsplit0
    rw [if_pos rfl, add_comm] at hsplit0'
    rw [← hsplit0']
    refine congrArg (fun t => (p.1 i - 1) + t) ?_
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    simp [hki]
  calc
    (∑ k : Idx n, (if k = i then p.1 k - 1 else p.1 k))
        = (p.1 i - 1) +
            Finset.sum ((Finset.univ : Finset (Idx n)).erase i) (fun k => p.1 k) := hsplit
    _ = (p.1 i + Finset.sum ((Finset.univ : Finset (Idx n)).erase i) (fun k => p.1 k)) - 1 := by
          omega
    _ = (∑ k : Idx n, p.1 k) - 1 := by
          simpa [add_comm] using congrArg (fun t => t - 1)
            (Finset.sum_erase_add (s := (Finset.univ : Finset (Idx n)))
              (a := i) (f := fun k : Idx n => p.1 k) hiU)
    _ = (m + 1) - 1 := by simp [p.2]
    _ = m := by omega

@[simp] theorem decrementCoord_apply_same (p : GridVertex n (m + 1)) (i : Idx n) (hi : 0 < p.1 i) :
    (decrementCoord p i hi).1 i = p.1 i - 1 := by
  classical
  simp [decrementCoord]

@[simp] theorem decrementCoord_apply_other (p : GridVertex n (m + 1)) (i k : Idx n)
    (hi : 0 < p.1 i) (hk : k ≠ i) :
    (decrementCoord p i hi).1 k = p.1 k := by
  classical
  simp [decrementCoord, hk]

/-- Decrementing one coordinate changes each raw integer coordinate by at most one. -/
theorem abs_sub_le_one_decrementCoord (p : GridVertex n (m + 1)) (i : Idx n) (hi : 0 < p.1 i) :
    ∀ k : Idx n, |(p.1 k : ℝ) - ((decrementCoord p i hi).1 k : ℝ)| ≤ 1 := by
  intro k
  by_cases hki : k = i
  · subst k
    rw [decrementCoord_apply_same]
    have hgei : 1 ≤ p.1 i := Nat.succ_le_iff.mpr hi
    have hcast : ((p.1 i - 1 : ℕ) : ℝ) = (p.1 i : ℝ) - 1 := by
      norm_num [Nat.cast_sub hgei]
    rw [hcast]
    ring_nf
    norm_num
  · rw [decrementCoord_apply_other _ _ _ hi hki]
    simp

/--
Transfer one unit from coordinate `j` to coordinate `i` (same denominator sum).
Implemented as increment at `i`, then decrement at `j`.
-/
def transferUnit (p : GridVertex n m) (i j : Idx n) (hne : i ≠ j) (hj : 0 < p.1 j) :
    GridVertex n m := by
  have hj' : 0 < (incrementCoord p i).1 j := by
    have hEq : (incrementCoord p i).1 j = p.1 j := incrementCoord_apply_other p i j hne.symm
    simpa [hEq] using hj
  exact decrementCoord (incrementCoord p i) j hj'

/-- `transferUnit` does not depend on the particular positivity witness. -/
theorem transferUnit_proof_irrel
    (p : GridVertex n m) (i j : Idx n) (hne : i ≠ j)
    {hj₁ hj₂ : 0 < p.1 j} :
    transferUnit (n := n) (m := m) p i j hne hj₁ =
      transferUnit (n := n) (m := m) p i j hne hj₂ := by
  cases Subsingleton.elim hj₁ hj₂
  rfl

@[simp] theorem transferUnit_apply_left (p : GridVertex n m) (i j : Idx n)
    (hne : i ≠ j) (hj : 0 < p.1 j) :
    (transferUnit p i j hne hj).1 i = p.1 i + 1 := by
  classical
  unfold transferUnit
  simp [decrementCoord_apply_other, incrementCoord_apply_same, hne]

@[simp] theorem transferUnit_apply_right (p : GridVertex n m) (i j : Idx n)
    (hne : i ≠ j) (hj : 0 < p.1 j) :
    (transferUnit p i j hne hj).1 j = p.1 j - 1 := by
  classical
  unfold transferUnit
  have hEq : (incrementCoord p i).1 j = p.1 j := incrementCoord_apply_other p i j hne.symm
  simp [decrementCoord_apply_same, hEq]

@[simp] theorem transferUnit_apply_other (p : GridVertex n m) (i j k : Idx n)
    (hne : i ≠ j) (hj : 0 < p.1 j) (hki : k ≠ i) (hkj : k ≠ j) :
    (transferUnit p i j hne hj).1 k = p.1 k := by
  classical
  unfold transferUnit
  simp [decrementCoord_apply_other, incrementCoord_apply_other, hki, hkj]

@[simp] theorem transferUnit_pos_left (p : GridVertex n m) (i j : Idx n)
    (hne : i ≠ j) (hj : 0 < p.1 j) :
    0 < (transferUnit p i j hne hj).1 i := by
  rw [transferUnit_apply_left (n := n) (m := m) p i j hne hj]
  exact Nat.succ_pos _

/-- Source index of step `r` in a permutation transfer chain. -/
def permStepSource (σ : Equiv.Perm (Idx n)) (r : Fin n) : Idx n :=
  σ ⟨r.1, Nat.lt_succ_of_lt r.2⟩

/-- Target index of step `r` in a permutation transfer chain. -/
def permStepTarget (σ : Equiv.Perm (Idx n)) (r : Fin n) : Idx n :=
  σ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩

theorem permStep_source_ne_target (σ : Equiv.Perm (Idx n)) (r : Fin n) :
    permStepSource (n := n) σ r ≠ permStepTarget (n := n) σ r := by
  intro hEq
  have hpre :
      (⟨r.1, Nat.lt_succ_of_lt r.2⟩ : Idx n) =
        (⟨r.1 + 1, Nat.succ_lt_succ r.2⟩ : Idx n) := by
    have hpre' : permStepSource (n := n) σ r = permStepTarget (n := n) σ r := hEq
    exact σ.injective hpre'
  have hval : r.1 = r.1 + 1 := by exact congrArg Fin.val hpre
  omega

/--
One-step transfer along permutation step `r`.
This is the local building block for ordered Kuhn transfer chains.
-/
def permStepTransfer (σ : Equiv.Perm (Idx n)) (r : Fin n)
    (p : GridVertex n m) (hsrc : 0 < p.1 (permStepSource (n := n) σ r)) :
    GridVertex n m :=
  transferUnit p (permStepTarget (n := n) σ r) (permStepSource (n := n) σ r)
    (permStep_source_ne_target (n := n) σ r).symm hsrc

/-- `permStepTransfer` does not depend on the particular source-positivity witness. -/
theorem permStepTransfer_proof_irrel
    (σ : Equiv.Perm (Idx n)) (r : Fin n) (p : GridVertex n m)
    {hsrc₁ hsrc₂ : 0 < p.1 (permStepSource (n := n) σ r)} :
    permStepTransfer (n := n) (m := m) σ r p hsrc₁ =
      permStepTransfer (n := n) (m := m) σ r p hsrc₂ := by
  unfold permStepTransfer
  exact transferUnit_proof_irrel (n := n) (m := m) p
    (permStepTarget (n := n) σ r) (permStepSource (n := n) σ r)
    (permStep_source_ne_target (n := n) σ r).symm

/-- `permStepTransfer` respects equality of the root vertex (proof arguments ignored). -/
theorem permStepTransfer_congr_root
    (σ : Equiv.Perm (Idx n)) (r : Fin n)
    {p q : GridVertex n m} (hpq : p = q)
    {hsrcP : 0 < p.1 (permStepSource (n := n) σ r)}
    {hsrcQ : 0 < q.1 (permStepSource (n := n) σ r)} :
    permStepTransfer (n := n) (m := m) σ r p hsrcP =
      permStepTransfer (n := n) (m := m) σ r q hsrcQ := by
  cases hpq
  exact permStepTransfer_proof_irrel (n := n) (m := m) σ r p

@[simp] theorem permStepTransfer_pos_target
    (σ : Equiv.Perm (Idx n)) (r : Fin n)
    (p : GridVertex n m) (hsrc : 0 < p.1 (permStepSource (n := n) σ r)) :
    0 < (permStepTransfer (n := n) (m := m) σ r p hsrc).1
      (permStepTarget (n := n) σ r) := by
  exact transferUnit_pos_left (n := n) (m := m)
    p (permStepTarget (n := n) σ r) (permStepSource (n := n) σ r)
    (permStep_source_ne_target (n := n) σ r).symm hsrc

/-- Consecutive permutation steps satisfy `source(r+1) = target(r)`. -/
@[simp] theorem permStepSource_succ_eq_permStepTarget
    (σ : Equiv.Perm (Idx n))
    (r : ℕ) (hr : r + 1 < n) :
    permStepSource (n := n) σ ⟨r + 1, hr⟩ =
      permStepTarget (n := n) σ ⟨r, Nat.lt_of_succ_lt hr⟩ := by
  simp [permStepSource, permStepTarget]

/--
Right-multiplying by `finRotate (n+1)` shifts step sources by one:
the shifted source at `r` is the original target at `r`.
-/
@[simp] theorem permStepSource_mul_finRotate
    (σ : Equiv.Perm (Idx n)) (r : Fin n) :
    permStepSource (n := n) (σ * finRotate (n + 1)) r =
      permStepTarget (n := n) σ r := by
  change (σ * finRotate (n + 1)) ⟨r.1, Nat.lt_succ_of_lt r.2⟩ =
      σ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩
  change σ ((finRotate (n + 1)) ⟨r.1, Nat.lt_succ_of_lt r.2⟩) =
      σ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩
  congr
  simpa using (finRotate_of_lt (n := n) (k := r.1) r.2)

/--
For non-last steps, right-multiplying by `finRotate (n+1)` also shifts targets by one.
-/
@[simp] theorem permStepTarget_mul_finRotate_of_lt
    (σ : Equiv.Perm (Idx n)) (r : Fin n)
    (hr : r.1 + 1 < n) :
    permStepTarget (n := n) (σ * finRotate (n + 1)) r =
      permStepTarget (n := n) σ ⟨r.1 + 1, hr⟩ := by
  change (σ * finRotate (n + 1)) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩ =
      σ ⟨r.1 + 2, Nat.succ_lt_succ hr⟩
  change σ ((finRotate (n + 1)) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩) =
      σ ⟨r.1 + 2, Nat.succ_lt_succ hr⟩
  congr
  simpa [Nat.add_assoc] using (finRotate_of_lt (n := n) (k := r.1 + 1) hr)

/--
Concrete step equality used in shifted-chain comparisons:
for `n ≥ 2`, step `0` of `σ * finRotate (n+1)` matches step `1` of `σ`
(up to source-positivity proof irrelevance).
-/
theorem permStepTransfer_mul_finRotate_zero_eq
    (h1n : 1 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (hsrcS : 0 < p.1 (permStepSource (n := n) (σ * finRotate (n + 1)) ⟨0, Nat.lt_trans Nat.zero_lt_one h1n⟩))
    (hsrcO : 0 < p.1 (permStepSource (n := n) σ ⟨1, h1n⟩)) :
    permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1))
      ⟨0, Nat.lt_trans Nat.zero_lt_one h1n⟩ p hsrcS
      =
    permStepTransfer (n := n) (m := m) σ ⟨1, h1n⟩ p hsrcO := by
  let hn : 0 < n := Nat.lt_trans Nat.zero_lt_one h1n
  let r0 : Fin n := ⟨0, hn⟩
  let r1 : Fin n := ⟨1, h1n⟩
  have hsrcEq :
      permStepSource (n := n) (σ * finRotate (n + 1)) r0 = permStepSource (n := n) σ r1 := by
    simp [permStepSource_mul_finRotate (n := n) (σ := σ) (r := r0), permStepTarget, r0, r1]
  have htarEq :
      permStepTarget (n := n) (σ * finRotate (n + 1)) r0 = permStepTarget (n := n) σ r1 := by
    simpa [r0, r1] using
      permStepTarget_mul_finRotate_of_lt (n := n) (σ := σ) (r := r0) h1n
  have hsrcS' : 0 < p.1 (permStepSource (n := n) σ r1) := by
    simpa [r0, hsrcEq] using hsrcS
  have hsrcO' : 0 < p.1 (permStepSource (n := n) σ r1) := by
    simpa [r1] using hsrcO
  have hproof : hsrcS' = hsrcO' := Subsingleton.elim _ _
  calc
    permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1)) r0 p hsrcS
        = transferUnit p (permStepTarget (n := n) σ r1) (permStepSource (n := n) σ r1)
            (permStep_source_ne_target (n := n) σ r1).symm hsrcS' := by
              simp [permStepTransfer, hsrcEq, htarEq, r0]
    _ = transferUnit p (permStepTarget (n := n) σ r1) (permStepSource (n := n) σ r1)
          (permStep_source_ne_target (n := n) σ r1).symm hsrcO' := by
            simpa [hproof] using
              transferUnit_proof_irrel (n := n) (m := m) p
                (permStepTarget (n := n) σ r1) (permStepSource (n := n) σ r1)
                (permStep_source_ne_target (n := n) σ r1).symm
    _ = permStepTransfer (n := n) (m := m) σ r1 p hsrcO := by
          simp [permStepTransfer, r1]

/--
General shifted-step equality:
for any `r` with `r+1 < n`, step `r` under `σ * finRotate (n+1)` matches
step `r+1` under `σ` (up to source-positivity proof irrelevance).
-/
theorem permStepTransfer_mul_finRotate_eq_succ
    (σ : Equiv.Perm (Idx n))
    (r : Fin n) (hr : r.1 + 1 < n)
    (p : GridVertex n m)
    (hsrcS : 0 < p.1 (permStepSource (n := n) (σ * finRotate (n + 1)) r))
    (hsrcO : 0 < p.1 (permStepSource (n := n) σ ⟨r.1 + 1, hr⟩)) :
    permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1)) r p hsrcS
      =
    permStepTransfer (n := n) (m := m) σ ⟨r.1 + 1, hr⟩ p hsrcO := by
  let r1 : Fin n := ⟨r.1 + 1, hr⟩
  have hsrcEq :
      permStepSource (n := n) (σ * finRotate (n + 1)) r = permStepSource (n := n) σ r1 := by
    calc
      permStepSource (n := n) (σ * finRotate (n + 1)) r
          = permStepTarget (n := n) σ r := by
              simp [permStepSource_mul_finRotate (n := n) (σ := σ) (r := r)]
      _ = permStepSource (n := n) σ r1 := by
            simpa [r1] using
              (permStepSource_succ_eq_permStepTarget (n := n) (σ := σ) r.1 hr).symm
  have htarEq :
      permStepTarget (n := n) (σ * finRotate (n + 1)) r = permStepTarget (n := n) σ r1 := by
    simpa [r1] using
      permStepTarget_mul_finRotate_of_lt (n := n) (σ := σ) (r := r) hr
  have hsrcS' : 0 < p.1 (permStepSource (n := n) σ r1) := by
    simpa [hsrcEq] using hsrcS
  have hsrcO' : 0 < p.1 (permStepSource (n := n) σ r1) := by
    simpa [r1] using hsrcO
  have hproof : hsrcS' = hsrcO' := Subsingleton.elim _ _
  calc
    permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1)) r p hsrcS
        = transferUnit p (permStepTarget (n := n) σ r1) (permStepSource (n := n) σ r1)
            (permStep_source_ne_target (n := n) σ r1).symm hsrcS' := by
              simp [permStepTransfer, hsrcEq, htarEq]
    _ = transferUnit p (permStepTarget (n := n) σ r1) (permStepSource (n := n) σ r1)
          (permStep_source_ne_target (n := n) σ r1).symm hsrcO' := by
            simpa [hproof] using
              transferUnit_proof_irrel (n := n) (m := m) p
                (permStepTarget (n := n) σ r1) (permStepSource (n := n) σ r1)
                (permStep_source_ne_target (n := n) σ r1).symm
    _ = permStepTransfer (n := n) (m := m) σ r1 p hsrcO := by
          simp [permStepTransfer, r1]

/--
Two consecutive permutation transfers (steps `r`, then `r+1`) from a vertex.
-/
def permTwoStepTransfer
    (σ : Equiv.Perm (Idx n))
    (r : ℕ) (hr : r + 1 < n)
    (p : GridVertex n m)
    (hsrc : 0 < p.1 (permStepSource (n := n) σ ⟨r, Nat.lt_of_succ_lt hr⟩)) :
    GridVertex n m := by
  let r0 : Fin n := ⟨r, Nat.lt_of_succ_lt hr⟩
  let q1 : GridVertex n m := permStepTransfer (n := n) (m := m) σ r0 p hsrc
  let hsrc1 : 0 < q1.1 (permStepSource (n := n) σ ⟨r + 1, hr⟩) := by
    have hposTarget :
        0 < q1.1 (permStepTarget (n := n) σ r0) :=
      permStepTransfer_pos_target (n := n) (m := m) σ r0 p hsrc
    have hEq :
        permStepSource (n := n) σ ⟨r + 1, hr⟩ = permStepTarget (n := n) σ r0 := by
      simp [r0, permStepSource, permStepTarget]
    rw [hEq]
    exact hposTarget
  exact permStepTransfer (n := n) (m := m) σ ⟨r + 1, hr⟩ q1 hsrc1

/--
Recursive permutation-chain states with carried positivity at the current chain index.
-/
def permChainStateWithPos
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) :
    (t : ℕ) → (ht : t ≤ n) →
      {q : GridVertex n m // 0 < q.1 (σ ⟨t, Nat.lt_succ_of_le ht⟩)}
  | 0, ht => ⟨p, by simpa using h0⟩
  | t + 1, hs => by
      let ht : t ≤ n := Nat.le_of_succ_le hs
      let prev := permChainStateWithPos σ p h0 t ht
      let r : Fin n := ⟨t, Nat.lt_of_succ_le hs⟩
      have hsrc :
          0 < prev.1.1 (permStepSource (n := n) σ r) := by
        simpa [permStepSource, r] using prev.2
      let q1 : GridVertex n m := permStepTransfer (n := n) (m := m) σ r prev.1 hsrc
      have hnext :
          0 < q1.1 (σ ⟨t + 1, Nat.lt_succ_of_le hs⟩) := by
        simpa [q1, permStepTarget, r] using
          permStepTransfer_pos_target (n := n) (m := m) σ r prev.1 hsrc
      exact ⟨q1, hnext⟩

/-- Vertex at position `t` in the permutation chain. -/
noncomputable def permChainVertex
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (t : Idx n) : GridVertex n m :=
  (permChainStateWithPos (n := n) (m := m) σ p h0 t.1 (Nat.le_of_lt_succ t.2)).1

@[simp] theorem permChainVertex_zero
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) :
    permChainVertex (n := n) (m := m) σ p h0 0 = p := by
  simp [permChainVertex, permChainStateWithPos]

theorem permChainVertex_pos_at_index
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (t : Idx n) :
    0 < (permChainVertex (n := n) (m := m) σ p h0 t).1 (σ t) := by
  dsimp [permChainVertex]
  simpa using (permChainStateWithPos (n := n) (m := m) σ p h0 t.1 (Nat.le_of_lt_succ t.2)).2

/--
Step recurrence: chain vertex at `r+1` is one permutation-step transfer
from the chain vertex at `r`.
-/
theorem permChainVertex_succ_eq_permStepTransfer
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) :
    ∃ hsrc : 0 < (permChainVertex (n := n) (m := m) σ p h0
          ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1 (permStepSource (n := n) σ r),
      permChainVertex (n := n) (m := m) σ p h0
          ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩ =
        permStepTransfer (n := n) (m := m) σ r
          (permChainVertex (n := n) (m := m) σ p h0
            ⟨r.1, Nat.lt_succ_of_lt r.2⟩) hsrc := by
  let t0 : Idx n := ⟨r.1, Nat.lt_succ_of_lt r.2⟩
  let t1 : Idx n := ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩
  have hpos0 : 0 < (permChainVertex (n := n) (m := m) σ p h0 t0).1 (σ t0) :=
    permChainVertex_pos_at_index (n := n) (m := m) σ p h0 t0
  have hsrc0 : 0 < (permChainVertex (n := n) (m := m) σ p h0 t0).1
      (permStepSource (n := n) σ r) := by
    simpa [permStepSource, t0]
      using hpos0
  refine ⟨hsrc0, ?_⟩
  dsimp [permChainVertex, t0, t1]
  simp [permChainStateWithPos]

/-- Cell generated by the full permutation transfer chain. -/
noncomputable def permChainCell
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) : Idx n → GridVertex n m :=
  fun t => permChainVertex (n := n) (m := m) σ p h0 t

/--
The first nontrivial chain vertex (`t = 1`) has positivity at the shifted-step source.
This is the exact positivity seed when restarting from `t = 1` with
the cyclically shifted permutation `σ * finRotate (n+1)`.
-/
theorem permChainCell_pos_at_shiftedSource_zero
    (hn : 0 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) :
    0 <
      ((permChainCell (n := n) (m := m) σ p h0) ⟨1, Nat.succ_lt_succ hn⟩).1
        (permStepSource (n := n) (σ * finRotate (n + 1)) ⟨0, hn⟩) := by
  have hpos1 :
      0 <
        ((permChainCell (n := n) (m := m) σ p h0) ⟨1, Nat.succ_lt_succ hn⟩).1
          (σ ⟨1, Nat.succ_lt_succ hn⟩) := by
    exact permChainVertex_pos_at_index (n := n) (m := m) σ p h0
      ⟨1, Nat.succ_lt_succ hn⟩
  simpa [permStepSource_mul_finRotate (n := n) (σ := σ) (r := ⟨0, hn⟩), permStepTarget]
    using hpos1

/--
At dimension `n ≥ 2`, the shifted chain rooted at original `t = 1` agrees at
its `t = 1` vertex with original `t = 2`.
-/
theorem permChainCell_shifted_one_eq_original_two
    (h1n : 1 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) :
    let hn : 0 < n := Nat.lt_trans Nat.zero_lt_one h1n
    let t1 : Idx n := ⟨1, Nat.succ_lt_succ hn⟩
    let t2 : Idx n := ⟨2, Nat.succ_lt_succ h1n⟩
    let q1 : GridVertex n m := (permChainCell (n := n) (m := m) σ p h0) t1
    let hq1 :
      0 < q1.1 (permStepSource (n := n) (σ * finRotate (n + 1)) ⟨0, hn⟩) :=
        permChainCell_pos_at_shiftedSource_zero (n := n) (m := m) hn σ p h0
    (permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1) t1
      = (permChainCell (n := n) (m := m) σ p h0) t2 := by
  let hn : 0 < n := Nat.lt_trans Nat.zero_lt_one h1n
  let t1 : Idx n := ⟨1, Nat.succ_lt_succ hn⟩
  let t2 : Idx n := ⟨2, Nat.succ_lt_succ h1n⟩
  let q1 : GridVertex n m := (permChainCell (n := n) (m := m) σ p h0) t1
  let hq1 :
      0 < q1.1 (permStepSource (n := n) (σ * finRotate (n + 1)) ⟨0, hn⟩) :=
    permChainCell_pos_at_shiftedSource_zero (n := n) (m := m) hn σ p h0
  let r0 : Fin n := ⟨0, hn⟩
  let r1 : Fin n := ⟨1, h1n⟩
  rcases permChainVertex_succ_eq_permStepTransfer
      (n := n) (m := m) (σ := (σ * finRotate (n + 1))) (p := q1) (h0 := hq1) r0 with
      ⟨hsrcS, hstepS⟩
  rcases permChainVertex_succ_eq_permStepTransfer
      (n := n) (m := m) (σ := σ) (p := p) (h0 := h0) r1 with
      ⟨hsrcO, hstepO⟩
  have hbaseShift :
      (permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1
          ⟨r0.1, Nat.lt_succ_of_lt r0.2⟩) = q1 := by
    simp [permChainCell, r0]
  have hbaseOrig :
      (permChainCell (n := n) (m := m) σ p h0
          ⟨r1.1, Nat.lt_succ_of_lt r1.2⟩) = q1 := by
    simp [q1, t1, r1]
  calc
    (permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1) t1
        = permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1)) r0 q1 hsrcS := by
            simpa [t1, r0, hbaseShift] using hstepS
    _ = permStepTransfer (n := n) (m := m) σ r1 q1 hsrcO := by
          exact permStepTransfer_mul_finRotate_zero_eq (n := n) (m := m) h1n σ q1
            (by simpa [r0] using hsrcS) (by simpa [hbaseOrig, r1] using hsrcO)
    _ = (permChainCell (n := n) (m := m) σ p h0) t2 := by
          simpa [t2, r1, hbaseOrig] using hstepO.symm

/--
Global shifted-chain alignment:
for every `t < n`, with shifted root at original `t = 1`,
`shifted[t] = original[t+1]`.
-/
theorem permChainCell_shifted_eq_original_succ
    (h1n : 1 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) :
    ∀ t : ℕ, ∀ ht : t < n,
      (permChainCell (n := n) (m := m) (σ * finRotate (n + 1))
          ((permChainCell (n := n) (m := m) σ p h0)
            ⟨1, Nat.succ_lt_succ (Nat.lt_trans Nat.zero_lt_one h1n)⟩)
          (permChainCell_pos_at_shiftedSource_zero (n := n) (m := m)
            (Nat.lt_trans Nat.zero_lt_one h1n) σ p h0))
          ⟨t, Nat.lt_succ_of_lt ht⟩
        =
      (permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.succ_lt_succ ht⟩ := by
  let hn : 0 < n := Nat.lt_trans Nat.zero_lt_one h1n
  let t1 : Idx n := ⟨1, Nat.succ_lt_succ hn⟩
  let q1 : GridVertex n m := (permChainCell (n := n) (m := m) σ p h0) t1
  let hq1 :
      0 < q1.1 (permStepSource (n := n) (σ * finRotate (n + 1)) ⟨0, hn⟩) :=
    permChainCell_pos_at_shiftedSource_zero (n := n) (m := m) hn σ p h0
  intro t ht
  revert ht
  refine Nat.rec ?_ ?_ t
  · intro ht0
    simp [permChainCell, q1, t1]
  · intro t ih ht
    have ht' : t < n := lt_trans (Nat.lt_succ_self t) ht
    let rS : Fin n := ⟨t, ht'⟩
    let rO : Fin n := ⟨t + 1, ht⟩
    rcases permChainVertex_succ_eq_permStepTransfer
        (n := n) (m := m) (σ := (σ * finRotate (n + 1))) (p := q1) (h0 := hq1) rS with
        ⟨hsrcS, hstepS⟩
    rcases permChainVertex_succ_eq_permStepTransfer
        (n := n) (m := m) (σ := σ) (p := p) (h0 := h0) rO with
        ⟨hsrcO, hstepO⟩
    have ihEq :
        (permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1)
            ⟨t, Nat.lt_succ_of_lt ht'⟩
          =
        (permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.succ_lt_succ ht'⟩ := ih ht'
    have hsrcS0 :
        0 < ((permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1)
                ⟨t, Nat.lt_succ_of_lt ht'⟩).1
              (permStepSource (n := n) (σ * finRotate (n + 1)) rS) := by
      simpa [permChainCell, rS] using hsrcS
    have hsrcS' :
        0 < ((permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.succ_lt_succ ht'⟩).1
              (permStepSource (n := n) (σ * finRotate (n + 1)) rS) := by
      simpa [ihEq] using hsrcS0
    have hsrcO' :
        0 < ((permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.succ_lt_succ ht'⟩).1
              (permStepSource (n := n) σ rO) := by
      simpa [rO] using hsrcO
    have hmove :
        permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1)) rS
            ((permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1)
              ⟨t, Nat.lt_succ_of_lt ht'⟩) hsrcS0
          =
        permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1)) rS
            ((permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.succ_lt_succ ht'⟩) hsrcS' := by
      exact permStepTransfer_congr_root (n := n) (m := m)
        (σ := (σ * finRotate (n + 1))) (r := rS) ihEq
    have hstepS' :
        (permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1)
            ⟨t + 1, Nat.lt_succ_of_lt ht⟩
          =
        permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1)) rS
            ((permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.succ_lt_succ ht'⟩) hsrcS' := by
      have hstepS0 :
          (permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1)
              ⟨t + 1, Nat.lt_succ_of_lt ht⟩
            =
          permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1)) rS
              ((permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1)
                ⟨t, Nat.lt_succ_of_lt ht'⟩) hsrcS0 := by
        simpa [permChainCell, rS] using hstepS
      exact hstepS0.trans hmove
    calc
      (permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1)
          ⟨t + 1, Nat.lt_succ_of_lt ht⟩
          =
        permStepTransfer (n := n) (m := m) (σ * finRotate (n + 1)) rS
          ((permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.succ_lt_succ ht'⟩) hsrcS' := hstepS'
      _ = permStepTransfer (n := n) (m := m) σ rO
            ((permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.succ_lt_succ ht'⟩) hsrcO' := by
            exact permStepTransfer_mul_finRotate_eq_succ (n := n) (m := m) σ rS ht
              ((permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.succ_lt_succ ht'⟩) hsrcS' hsrcO'
      _ = (permChainCell (n := n) (m := m) σ p h0) ⟨t + 2, Nat.succ_lt_succ ht⟩ := by
            simpa [rO] using hstepO.symm

/--
Index-typed corollary of shifted-chain alignment:
for every `k : Fin n`, `shifted[k] = original[k+1]`.
-/
theorem permChainCell_shifted_eq_original_succ_idx
    (h1n : 1 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Fin n) :
    let hn : 0 < n := Nat.lt_trans Nat.zero_lt_one h1n
    let t1 : Idx n := ⟨1, Nat.succ_lt_succ hn⟩
    let q1 : GridVertex n m := (permChainCell (n := n) (m := m) σ p h0) t1
    let hq1 :
      0 < q1.1 (permStepSource (n := n) (σ * finRotate (n + 1)) ⟨0, hn⟩) :=
        permChainCell_pos_at_shiftedSource_zero (n := n) (m := m) hn σ p h0
    (permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1)
        ⟨k.1, Nat.lt_succ_of_lt k.2⟩
      =
    (permChainCell (n := n) (m := m) σ p h0)
        ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩ := by
  simpa using
    (permChainCell_shifted_eq_original_succ (n := n) (m := m) h1n σ p h0 k.1 k.2)

/--
Commutation identity for two transfers on distinct indices:
moving `j → k` and then `k → i` equals the direct move `j → i`.
-/
theorem transferUnit_transferUnit_eq
    (p : GridVertex n m) (i k j : Idx n)
    (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (hj : 0 < p.1 j)
    (hk : 0 < (transferUnit p k j hkj hj).1 k) :
    transferUnit (transferUnit p k j hkj hj) i k hik hk =
      transferUnit p i j hij hj := by
  ext t
  by_cases hti : t = i
  · subst t
    rw [transferUnit_apply_left (n := n) (m := m)
      (transferUnit p k j hkj hj) i k hik hk]
    rw [transferUnit_apply_left (n := n) (m := m) p i j hij hj]
    rw [transferUnit_apply_other (n := n) (m := m) p k j i hkj hj hik hij]
  · by_cases htj : t = j
    · subst t
      rw [transferUnit_apply_other (n := n) (m := m)
        (transferUnit p k j hkj hj) i k j hik hk hij.symm hkj.symm]
      rw [transferUnit_apply_right (n := n) (m := m) p k j hkj hj]
      rw [transferUnit_apply_right (n := n) (m := m) p i j hij hj]
    · by_cases htk : t = k
      · subst t
        rw [transferUnit_apply_right (n := n) (m := m)
          (transferUnit p k j hkj hj) i k hik hk]
        rw [transferUnit_apply_left (n := n) (m := m) p k j hkj hj]
        rw [transferUnit_apply_other (n := n) (m := m) p i j k hij hj hik.symm hkj]
        omega
      · rw [transferUnit_apply_other (n := n) (m := m)
          (transferUnit p k j hkj hj) i k t hik hk hti htk]
        rw [transferUnit_apply_other (n := n) (m := m) p k j t hkj hj htk htj]
        rw [transferUnit_apply_other (n := n) (m := m) p i j t hij hj hti htj]

/-- Inverse cancellation of opposite transfer moves on a pair of coordinates. -/
theorem transferUnit_cancel_opposite
    (p : GridVertex n m) (k j : Idx n)
    (hkj : k ≠ j) (hj : 0 < p.1 j)
    (hk : 0 < (transferUnit p k j hkj hj).1 k) :
    transferUnit (transferUnit p k j hkj hj) j k hkj.symm hk = p := by
  ext t
  by_cases htj : t = j
  · subst t
    rw [transferUnit_apply_left (n := n) (m := m)
      (transferUnit p k j hkj hj) j k hkj.symm hk]
    rw [transferUnit_apply_right (n := n) (m := m) p k j hkj hj]
    omega
  · by_cases htk : t = k
    · subst t
      rw [transferUnit_apply_right (n := n) (m := m)
        (transferUnit p k j hkj hj) j k hkj.symm hk]
      rw [transferUnit_apply_left (n := n) (m := m) p k j hkj hj]
      omega
    · rw [transferUnit_apply_other (n := n) (m := m)
        (transferUnit p k j hkj hj) j k t hkj.symm hk htj htk]
      rw [transferUnit_apply_other (n := n) (m := m) p k j t hkj hj htk htj]

/-- A transfer move changes each coordinate by at most one in absolute value. -/
theorem coordDiffLeOne_transferUnit (p : GridVertex n m) (i j : Idx n)
    (hne : i ≠ j) (hj : 0 < p.1 j) :
    CoordDiffLeOne p (transferUnit p i j hne hj) := by
  intro k
  by_cases hki : k = i
  · subst k
    rw [transferUnit_apply_left _ _ _ hne hj]
    norm_num
  · by_cases hkj : k = j
    · subst k
      rw [transferUnit_apply_right _ _ _ hne hj]
      have hgej : 1 ≤ p.1 j := Nat.succ_le_iff.mpr hj
      have hcast : ((p.1 j - 1 : ℕ) : ℝ) = (p.1 j : ℝ) - 1 := by
        norm_num [Nat.cast_sub hgej]
      rw [hcast]
      ring_nf
      norm_num
    · rw [transferUnit_apply_other _ _ _ _ hne hj hki hkj]
      simp

/-- Symmetry of the coordinatewise mesh relation. -/
theorem coordDiffLeOne_symm {p q : GridVertex n m}
    (h : CoordDiffLeOne p q) :
    CoordDiffLeOne q p := by
  intro k
  simpa [abs_sub_comm] using h k

/--
Two transfers from the same source coordinate are mesh-adjacent.
-/
theorem coordDiffLeOne_transferUnit_pair (p : GridVertex n m)
    (i i' j : Idx n)
    (hij : i ≠ j) (hi'j : i' ≠ j)
    (hj : 0 < p.1 j) :
    CoordDiffLeOne (transferUnit p i j hij hj) (transferUnit p i' j hi'j hj) := by
  intro k
  by_cases hii' : i = i'
  · subst i'
    simp
  · by_cases hkj : k = j
    · subst k
      rw [transferUnit_apply_right _ _ _ hij hj, transferUnit_apply_right _ _ _ hi'j hj]
      simp
    · by_cases hki : k = i
      · subst k
        rw [transferUnit_apply_left _ _ _ hij hj]
        rw [transferUnit_apply_other (p := p) (i := i') (j := j) (k := i)
          hi'j hj hii' hkj]
        norm_num
      · by_cases hki' : k = i'
        · subst k
          rw [transferUnit_apply_other (p := p) (i := i) (j := j) (k := i')
            hij hj (by intro h; exact hii' h.symm) hkj]
          rw [transferUnit_apply_left _ _ _ hi'j hj]
          norm_num [abs_sub_comm]
        · rw [transferUnit_apply_other _ _ _ _ hij hj hki hkj]
          rw [transferUnit_apply_other _ _ _ _ hi'j hj hki' hkj]
          simp

/-- Consecutive vertices in a permutation-chain cell are mesh-adjacent. -/
theorem coordDiffLeOne_permChainCell_succ
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) :
    CoordDiffLeOne
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩)
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩) := by
  change CoordDiffLeOne
    (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1, Nat.lt_succ_of_lt r.2⟩)
    (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩)
  rcases permChainVertex_succ_eq_permStepTransfer (n := n) (m := m) σ p h0 r with ⟨hsrc, hs⟩
  rw [hs]
  exact coordDiffLeOne_transferUnit (n := n) (m := m)
    (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1, Nat.lt_succ_of_lt r.2⟩)
    (permStepTarget (n := n) σ r) (permStepSource (n := n) σ r)
    (permStep_source_ne_target (n := n) σ r).symm hsrc

theorem permChainCell_succ_ne
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) :
    (permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩
      ≠
    (permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩ := by
  rcases permChainVertex_succ_eq_permStepTransfer (n := n) (m := m) σ p h0 r with ⟨hsrc, hs⟩
  intro hEq
  have hcoord :
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
        (permStepTarget (n := n) σ r)
        =
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
        (permStepTarget (n := n) σ r) := by
    simpa using congrArg
      (fun q : GridVertex n m => q.1 (permStepTarget (n := n) σ r)) hEq.symm
  change
      (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
        (permStepTarget (n := n) σ r)
        =
      (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
        (permStepTarget (n := n) σ r) at hcoord
  rw [hs] at hcoord
  simp [permStepTransfer, transferUnit_apply_left] at hcoord

@[simp] theorem permChainCell_succ_apply_target
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
        (permStepTarget (n := n) σ r)
      =
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
        (permStepTarget (n := n) σ r) + 1 := by
  change (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
      (permStepTarget (n := n) σ r)
    =
    (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
      (permStepTarget (n := n) σ r) + 1
  rcases permChainVertex_succ_eq_permStepTransfer (n := n) (m := m) σ p h0 r with ⟨hsrc, hs⟩
  rw [hs]
  exact transferUnit_apply_left (n := n) (m := m)
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩)
    (permStepTarget (n := n) σ r) (permStepSource (n := n) σ r)
    (permStep_source_ne_target (n := n) σ r).symm hsrc

@[simp] theorem permChainCell_succ_apply_source
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
        (permStepSource (n := n) σ r)
      =
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
        (permStepSource (n := n) σ r) - 1 := by
  change (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
      (permStepSource (n := n) σ r)
    =
    (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
      (permStepSource (n := n) σ r) - 1
  rcases permChainVertex_succ_eq_permStepTransfer (n := n) (m := m) σ p h0 r with ⟨hsrc, hs⟩
  rw [hs]
  exact transferUnit_apply_right (n := n) (m := m)
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩)
    (permStepTarget (n := n) σ r) (permStepSource (n := n) σ r)
    (permStep_source_ne_target (n := n) σ r).symm hsrc

@[simp] theorem permChainCell_succ_apply_other
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) (i : Idx n)
    (hiT : i ≠ permStepTarget (n := n) σ r)
    (hiS : i ≠ permStepSource (n := n) σ r) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1 i
      =
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1 i := by
  change (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1 i
    =
    (permChainVertex (n := n) (m := m) σ p h0 ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1 i
  rcases permChainVertex_succ_eq_permStepTransfer (n := n) (m := m) σ p h0 r with ⟨hsrc, hs⟩
  rw [hs]
  exact transferUnit_apply_other (n := n) (m := m)
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩)
    (permStepTarget (n := n) σ r) (permStepSource (n := n) σ r) i
    (permStep_source_ne_target (n := n) σ r).symm hsrc hiT hiS

@[simp] theorem permChainCell_succ_apply_sigma_r
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
        (σ ⟨r.1, Nat.lt_succ_of_lt r.2⟩)
      =
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
        (σ ⟨r.1, Nat.lt_succ_of_lt r.2⟩) - 1 := by
  simpa [permStepSource] using
    permChainCell_succ_apply_source (n := n) (m := m) σ p h0 r

@[simp] theorem permChainCell_succ_apply_sigma_rsucc
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
        (σ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩)
      =
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
        (σ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩) + 1 := by
  simpa [permStepTarget] using
    permChainCell_succ_apply_target (n := n) (m := m) σ p h0 r

@[simp] theorem permChainCell_succ_apply_sigma_other
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) (k : Idx n)
    (hk_r : k ≠ ⟨r.1, Nat.lt_succ_of_lt r.2⟩)
    (hk_rsucc : k ≠ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
        (σ k)
      =
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
        (σ k) := by
  have hiT : σ k ≠ permStepTarget (n := n) σ r := by
    intro h
    apply hk_rsucc
    exact σ.injective (by simpa [permStepTarget] using h)
  have hiS : σ k ≠ permStepSource (n := n) σ r := by
    intro h
    apply hk_r
    exact σ.injective (by simpa [permStepSource] using h)
  simpa using
    permChainCell_succ_apply_other (n := n) (m := m) σ p h0 r (σ k) hiT hiS

/--
Piecewise one-step transition at coordinate `σ k`:
decrement at `k = r`, increment at `k = r+1`, unchanged otherwise.
-/
theorem permChainCell_succ_apply_sigma_cases
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) (k : Idx n) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1 (σ k)
      =
    (if _ : k = ⟨r.1, Nat.lt_succ_of_lt r.2⟩ then
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1 (σ k) - 1
    else if _ : k = ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩ then
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1 (σ k) + 1
    else
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1 (σ k)) := by
  by_cases hk_r : k = ⟨r.1, Nat.lt_succ_of_lt r.2⟩
  · subst hk_r
    simp [permChainCell_succ_apply_sigma_r]
  · by_cases hk_rsucc : k = ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩
    · subst hk_rsucc
      simp [hk_r, permChainCell_succ_apply_sigma_rsucc]
    · simp [hk_r, hk_rsucc, permChainCell_succ_apply_sigma_other]

@[simp] theorem permChainCell_one_apply_sigma0
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (hn : 0 < n) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨1, Nat.succ_lt_succ hn⟩).1 (σ 0)
      = p.1 (σ 0) - 1 := by
  let r0 : Fin n := ⟨0, hn⟩
  have hstep := permChainCell_succ_apply_sigma_r (n := n) (m := m) σ p h0 r0
  simpa [r0, permChainCell, permChainVertex_zero] using hstep

theorem permChainCell_succ_apply_sigma0_of_pos
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (r : Fin n) (hr : 0 < r.1) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1 (σ 0)
      =
    ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1 (σ 0) := by
  have hk_r : (0 : Idx n) ≠ ⟨r.1, Nat.lt_succ_of_lt r.2⟩ := by
    intro h
    have : (0 : ℕ) = r.1 := congrArg Fin.val h
    exact (Nat.ne_of_gt hr) this.symm
  have hk_rsucc : (0 : Idx n) ≠ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩ := by
    intro h
    have : (0 : ℕ) = r.1 + 1 := congrArg Fin.val h
    omega
  simpa using
    permChainCell_succ_apply_sigma_other (n := n) (m := m) σ p h0 r 0 hk_r hk_rsucc

/--
Closed form for the `σ 0` coordinate along the permutation chain:
it drops by one at step `1` and then stays constant.
-/
theorem permChainCell_apply_sigma0_nat
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (hn : 0 < n) :
    ∀ (t : ℕ) (ht : t ≤ n),
      ((permChainCell (n := n) (m := m) σ p h0) ⟨t, Nat.lt_succ_of_le ht⟩).1 (σ 0)
        = (if t = 0 then p.1 (σ 0) else p.1 (σ 0) - 1)
  | 0, ht => by
      simp [permChainCell, permChainVertex_zero]
  | t + 1, hs => by
      by_cases ht0 : t = 0
      · subst t
        have h1 :
            ((permChainCell (n := n) (m := m) σ p h0) ⟨1, Nat.succ_lt_succ hn⟩).1 (σ 0)
              = p.1 (σ 0) - 1 :=
          permChainCell_one_apply_sigma0 (n := n) (m := m) σ p h0 hn
        simpa using h1
      · have hpos : 0 < t := Nat.pos_of_ne_zero ht0
        let r : Fin n := ⟨t, Nat.lt_of_succ_le hs⟩
        let tIdx : Idx n := ⟨t, Nat.lt_succ_of_lt (Nat.lt_of_succ_le hs)⟩
        let t1Idx : Idx n := ⟨t + 1, Nat.lt_succ_of_le hs⟩
        have hstep :
            ((permChainCell (n := n) (m := m) σ p h0) t1Idx).1 (σ 0)
              = ((permChainCell (n := n) (m := m) σ p h0) tIdx).1 (σ 0) := by
          simpa [r, tIdx, t1Idx] using
            permChainCell_succ_apply_sigma0_of_pos (n := n) (m := m) σ p h0 r hpos
        have hprev :
            ((permChainCell (n := n) (m := m) σ p h0) tIdx).1 (σ 0) = p.1 (σ 0) - 1 := by
          have :=
            permChainCell_apply_sigma0_nat (σ := σ) (p := p) (h0 := h0) (hn := hn)
              t (Nat.le_of_succ_le hs)
          simpa [ht0, tIdx] using this
        rw [hstep, hprev]
        simp

theorem abs_sub_le_one_permChainCell_sigma0
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (hn : 0 < n)
    (t u : Idx n) :
    |(((permChainCell (n := n) (m := m) σ p h0 t).1 (σ 0) : ℝ) -
      ((permChainCell (n := n) (m := m) σ p h0 u).1 (σ 0) : ℝ))| ≤ 1 := by
  have ht :=
    permChainCell_apply_sigma0_nat (n := n) (m := m) (σ := σ) (p := p) (h0 := h0) (hn := hn)
      t.1 (Nat.le_of_lt_succ t.2)
  have hu :=
    permChainCell_apply_sigma0_nat (n := n) (m := m) (σ := σ) (p := p) (h0 := h0) (hn := hn)
      u.1 (Nat.le_of_lt_succ u.2)
  have hge : 1 ≤ p.1 (σ 0) := Nat.succ_le_iff.mpr h0
  by_cases ht0 : t.1 = 0 <;> by_cases hu0 : u.1 = 0
  · rw [ht, hu]
    simp [ht0, hu0]
  · rw [ht, hu]
    simp [ht0, hu0, Nat.cast_sub hge]
  · rw [ht, hu]
    simp [ht0, hu0, Nat.cast_sub hge]
  · rw [ht, hu]
    simp [ht0, hu0]

/--
At any nonzero chain index, coordinate `σ 0` has dropped by one.
-/
theorem permChainCell_apply_sigma0_of_ne_zero
    (hn : 0 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Idx n)
    (hk0 : k ≠ 0) :
    ((permChainCell (n := n) (m := m) σ p h0) k).1 (σ 0) = p.1 (σ 0) - 1 := by
  have hk0v : k.1 ≠ 0 := by
    intro h
    apply hk0
    exact Fin.ext h
  have hnat :
      ((permChainCell (n := n) (m := m) σ p h0)
        ⟨k.1, Nat.lt_succ_of_le (Nat.le_of_lt_succ k.2)⟩).1 (σ 0)
        = if k.1 = 0 then p.1 (σ 0) else p.1 (σ 0) - 1 := by
    exact permChainCell_apply_sigma0_nat (n := n) (m := m)
      (σ := σ) (p := p) (h0 := h0) (hn := hn) k.1 (Nat.le_of_lt_succ k.2)
  have hkcast : (⟨k.1, Nat.lt_succ_of_le (Nat.le_of_lt_succ k.2)⟩ : Idx n) = k := by
    apply Fin.ext
    simp
  simpa [hkcast, hk0v] using hnat

theorem permChainCell_apply_sigma_pos_of_lt
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Idx n) (hk : 0 < k.1) :
    ∀ (t : ℕ) (ht : t ≤ n), t < k.1 →
      ((permChainCell (n := n) (m := m) σ p h0) ⟨t, Nat.lt_succ_of_le ht⟩).1 (σ k)
        = p.1 (σ k)
  | 0, ht, hlt => by
      simp [permChainCell, permChainVertex_zero]
  | t + 1, hs, hlt => by
      let r : Fin n := ⟨t, Nat.lt_of_succ_le hs⟩
      have hk_r : k ≠ ⟨r.1, Nat.lt_succ_of_lt r.2⟩ := by
        intro h
        have : k.1 = t := congrArg Fin.val h
        omega
      have hk_rsucc : k ≠ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩ := by
        intro h
        have : k.1 = t + 1 := congrArg Fin.val h
        omega
      have hstep :
          ((permChainCell (n := n) (m := m) σ p h0) ⟨t + 1, Nat.lt_succ_of_le hs⟩).1 (σ k)
            =
          ((permChainCell (n := n) (m := m) σ p h0) ⟨t, Nat.lt_succ_of_lt (Nat.lt_of_succ_le hs)⟩).1
            (σ k) := by
        simpa [r] using
          permChainCell_succ_apply_sigma_other (n := n) (m := m) σ p h0 r k hk_r hk_rsucc
      have hprev :
          ((permChainCell (n := n) (m := m) σ p h0) ⟨t, Nat.lt_succ_of_lt (Nat.lt_of_succ_le hs)⟩).1
            (σ k) = p.1 (σ k) := by
        have : t < k.1 := by omega
        exact permChainCell_apply_sigma_pos_of_lt (σ := σ) (p := p) (h0 := h0) (k := k) (hk := hk)
          t (Nat.le_of_succ_le hs) this
      rw [hstep, hprev]

theorem permChainCell_apply_sigma_pos_at_self
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Idx n) (hk : 0 < k.1) :
    ((permChainCell (n := n) (m := m) σ p h0) k).1 (σ k) = p.1 (σ k) + 1 := by
  have hkm1_lt_n : k.1 - 1 < n := by
    have hklt : k.1 < n + 1 := k.2
    omega
  let r : Fin n := ⟨k.1 - 1, hkm1_lt_n⟩
  have hk_eq : k = ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩ := by
    apply Fin.ext
    dsimp [r]
    omega
  have hprev :
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1 (σ k)
        = p.1 (σ k) := by
    have hlt : r.1 < k.1 := by
      dsimp [r]
      omega
    exact permChainCell_apply_sigma_pos_of_lt (n := n) (m := m) σ p h0 k hk
      r.1 (Nat.le_of_lt r.2) hlt
  have hstep :
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
          (σ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩)
        =
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
          (σ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩) + 1 := by
    exact permChainCell_succ_apply_sigma_rsucc (n := n) (m := m) σ p h0 r
  rw [← hk_eq] at hstep
  rw [hstep, hprev]

theorem permChainCell_apply_sigma_pos_at_succ
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Idx n) (hk : 0 < k.1)
    (hkn : k.1 < n) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨k.1 + 1, Nat.succ_lt_succ hkn⟩).1 (σ k)
      = p.1 (σ k) := by
  let r : Fin n := ⟨k.1, hkn⟩
  have hk_eq : k = ⟨r.1, Nat.lt_succ_of_lt r.2⟩ := by
    apply Fin.ext
    simp [r]
  have hstep :
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩).1
          (σ ⟨r.1, Nat.lt_succ_of_lt r.2⟩)
        =
      ((permChainCell (n := n) (m := m) σ p h0) ⟨r.1, Nat.lt_succ_of_lt r.2⟩).1
          (σ ⟨r.1, Nat.lt_succ_of_lt r.2⟩) - 1 := by
    exact permChainCell_succ_apply_sigma_r (n := n) (m := m) σ p h0 r
  rw [← hk_eq] at hstep
  have hself :
      ((permChainCell (n := n) (m := m) σ p h0) k).1 (σ k) = p.1 (σ k) + 1 :=
    permChainCell_apply_sigma_pos_at_self (n := n) (m := m) σ p h0 k hk
  rw [hstep, hself]
  omega

theorem permChainCell_apply_sigma_pos_of_ge_succ
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Idx n) (hk : 0 < k.1) :
    ∀ (t : ℕ), k.1 + 1 ≤ t → ∀ htn : t ≤ n,
      ((permChainCell (n := n) (m := m) σ p h0) ⟨t, Nat.lt_succ_of_le htn⟩).1 (σ k)
        = p.1 (σ k) := by
  intro t hks htn
  let P : (s : ℕ) → k.1 + 1 ≤ s → Prop :=
    fun s _ =>
      ∀ hsN : s ≤ n,
        ((permChainCell (n := n) (m := m) σ p h0) ⟨s, Nat.lt_succ_of_le hsN⟩).1 (σ k)
          = p.1 (σ k)
  have hbase : P (k.1 + 1) (Nat.le_refl _) := by
    intro hsN
    have hkn : k.1 < n := by omega
    simpa using
      permChainCell_apply_sigma_pos_at_succ (n := n) (m := m) σ p h0 k hk hkn
  have hstep :
      ∀ s hs, P s hs → P (s + 1) (Nat.le_trans hs (Nat.le_succ s)) := by
    intro s hs ih hs1N
    have hsN : s ≤ n := Nat.le_of_succ_le hs1N
    have hprev :
        ((permChainCell (n := n) (m := m) σ p h0) ⟨s, Nat.lt_succ_of_le hsN⟩).1 (σ k)
          = p.1 (σ k) := ih hsN
    let r : Fin n := ⟨s, Nat.lt_of_succ_le hs1N⟩
    have hk_r : k ≠ ⟨r.1, Nat.lt_succ_of_lt r.2⟩ := by
      intro hEq
      have : k.1 = s := congrArg Fin.val hEq
      omega
    have hk_rsucc : k ≠ ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩ := by
      intro hEq
      have : k.1 = s + 1 := congrArg Fin.val hEq
      omega
    have hsame :
        ((permChainCell (n := n) (m := m) σ p h0) ⟨s + 1, Nat.lt_succ_of_le hs1N⟩).1 (σ k)
          =
        ((permChainCell (n := n) (m := m) σ p h0) ⟨s, Nat.lt_succ_of_lt (Nat.lt_of_succ_le hs1N)⟩).1
          (σ k) := by
      simpa [r] using
        permChainCell_succ_apply_sigma_other (n := n) (m := m) σ p h0 r k hk_r hk_rsucc
    rw [hsame, hprev]
  exact Nat.le_induction hbase hstep t hks htn

theorem permChainCell_apply_sigma_pos_of_gt
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Idx n) (hk : 0 < k.1)
    (t : ℕ) (ht : t ≤ n) (hgt : k.1 < t) :
    ((permChainCell (n := n) (m := m) σ p h0) ⟨t, Nat.lt_succ_of_le ht⟩).1 (σ k)
      = p.1 (σ k) := by
  have hks : k.1 + 1 ≤ t := by omega
  exact permChainCell_apply_sigma_pos_of_ge_succ (n := n) (m := m) σ p h0 k hk t hks ht

theorem permChainCell_apply_sigma_pos_nat
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Idx n) (hk : 0 < k.1) :
    ∀ (t : ℕ) (ht : t ≤ n),
      ((permChainCell (n := n) (m := m) σ p h0) ⟨t, Nat.lt_succ_of_le ht⟩).1 (σ k)
        = p.1 (σ k) + (if t = k.1 then 1 else 0)
  | t, ht => by
      let tIdx : Idx n := ⟨t, Nat.lt_succ_of_le ht⟩
      by_cases hlt : t < k.1
      · have hbase := permChainCell_apply_sigma_pos_of_lt (n := n) (m := m) σ p h0 k hk t ht hlt
        have hneq : t ≠ k.1 := Nat.ne_of_lt hlt
        simpa [hneq] using hbase
      · by_cases heq : t = k.1
        · have hidx : tIdx = k := by
            apply Fin.ext
            simpa [tIdx] using heq
          have hself :=
            permChainCell_apply_sigma_pos_at_self (n := n) (m := m) σ p h0 k hk
          simpa [hidx, heq] using hself
        · have hgt : k.1 < t := by omega
          have hbase := permChainCell_apply_sigma_pos_of_gt (n := n) (m := m) σ p h0 k hk t ht hgt
          simpa [heq] using hbase

/--
At positive chain index `k`, the chain vertex equals one unit transfer
from source `σ 0` to target `σ k` in the original root `p`.
-/
theorem permChainCell_eq_transfer_of_pos
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Idx n) (hk : 0 < k.1) :
    (permChainCell (n := n) (m := m) σ p h0) k =
      transferUnit (n := n) (m := m) p (σ k) (σ 0)
        (by
          intro hEq
          apply hk.ne'
          exact congrArg Fin.val (σ.injective hEq)) h0 := by
  have hn : 0 < n := lt_of_lt_of_le hk (Nat.le_of_lt_succ k.2)
  ext i
  obtain ⟨ℓ, rfl⟩ := σ.surjective i
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    have hL :
        ((permChainCell (n := n) (m := m) σ p h0) k).1 (σ 0) = p.1 (σ 0) - 1 :=
      permChainCell_apply_sigma0_of_ne_zero (n := n) (m := m) hn σ p h0 k (by
        intro hk0
        exact hk.ne' (congrArg Fin.val hk0))
    have hR :
        (transferUnit (n := n) (m := m) p (σ k) (σ 0)
          (by
            intro hEq
            apply hk.ne'
            exact congrArg Fin.val (σ.injective hEq)) h0).1 (σ 0)
          = p.1 (σ 0) - 1 := by
      exact transferUnit_apply_right (n := n) (m := m) p (σ k) (σ 0)
        (by
          intro hEq
          apply hk.ne'
          exact congrArg Fin.val (σ.injective hEq)) h0
    simpa [hL, hR]
  · by_cases hℓk : ℓ = k
    · subst ℓ
      have hL :
          ((permChainCell (n := n) (m := m) σ p h0) k).1 (σ k) = p.1 (σ k) + 1 :=
        permChainCell_apply_sigma_pos_at_self (n := n) (m := m) σ p h0 k hk
      have hR :
          (transferUnit (n := n) (m := m) p (σ k) (σ 0)
            (by
              intro hEq
              apply hk.ne'
              exact congrArg Fin.val (σ.injective hEq)) h0).1 (σ k)
            = p.1 (σ k) + 1 := by
        exact transferUnit_apply_left (n := n) (m := m) p (σ k) (σ 0)
          (by
            intro hEq
            apply hk.ne'
            exact congrArg Fin.val (σ.injective hEq)) h0
      simpa [hL, hR]
    · have hℓpos : 0 < ℓ.1 := by
        apply Nat.pos_of_ne_zero
        intro hℓz
        apply hℓ0
        exact Fin.ext hℓz
      have hneVal : ℓ.1 ≠ k.1 := by
        intro hEq
        apply hℓk
        exact Fin.ext hEq
      have hlt_or_hgt : ℓ.1 < k.1 ∨ k.1 < ℓ.1 := lt_or_gt_of_ne hneVal
      have hL :
          ((permChainCell (n := n) (m := m) σ p h0) k).1 (σ ℓ) = p.1 (σ ℓ) := by
        rcases hlt_or_hgt with hlt | hgt
        · exact permChainCell_apply_sigma_pos_of_gt (n := n) (m := m) σ p h0 ℓ hℓpos
            k.1 (Nat.le_of_lt_succ k.2) hlt
        · exact permChainCell_apply_sigma_pos_of_lt (n := n) (m := m) σ p h0 ℓ hℓpos
            k.1 (Nat.le_of_lt_succ k.2) hgt
      have hR :
          (transferUnit (n := n) (m := m) p (σ k) (σ 0)
            (by
              intro hEq
              apply hk.ne'
              exact congrArg Fin.val (σ.injective hEq)) h0).1 (σ ℓ)
            = p.1 (σ ℓ) := by
        exact transferUnit_apply_other (n := n) (m := m) p (σ k) (σ 0) (σ ℓ)
          (by
            intro hEq
            apply hk.ne'
            exact congrArg Fin.val (σ.injective hEq)) h0
          (by
            intro hEq
            apply hℓk
            exact σ.injective hEq)
          (by
            intro hEq
            apply hℓ0
            exact σ.injective hEq)
      simpa [hL, hR]

theorem abs_sub_le_one_permChainCell_sigma_pos
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (k : Idx n) (hk : 0 < k.1)
    (t u : Idx n) :
    |(((permChainCell (n := n) (m := m) σ p h0 t).1 (σ k) : ℝ) -
      ((permChainCell (n := n) (m := m) σ p h0 u).1 (σ k) : ℝ))| ≤ 1 := by
  have ht :=
    permChainCell_apply_sigma_pos_nat (n := n) (m := m)
      (σ := σ) (p := p) (h0 := h0) (k := k) (hk := hk)
      t.1 (Nat.le_of_lt_succ t.2)
  have hu :=
    permChainCell_apply_sigma_pos_nat (n := n) (m := m)
      (σ := σ) (p := p) (h0 := h0) (k := k) (hk := hk)
      u.1 (Nat.le_of_lt_succ u.2)
  rw [ht, hu]
  by_cases htEq : t.1 = k.1 <;> by_cases huEq : u.1 = k.1 <;> simp [htEq, huEq]

theorem permChainCell_ne_of_lt
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (t u : Idx n)
    (htu : t.1 < u.1) :
    (permChainCell (n := n) (m := m) σ p h0 t)
      ≠
    (permChainCell (n := n) (m := m) σ p h0 u) := by
  have huPos : 0 < u.1 := by
    apply Nat.pos_of_ne_zero
    intro hu0
    omega
  have htVal :
      ((permChainCell (n := n) (m := m) σ p h0) t).1 (σ u) = p.1 (σ u) :=
    permChainCell_apply_sigma_pos_of_lt (n := n) (m := m) σ p h0 u huPos
      t.1 (Nat.le_of_lt_succ t.2) htu
  have huVal :
      ((permChainCell (n := n) (m := m) σ p h0) u).1 (σ u) = p.1 (σ u) + 1 :=
    permChainCell_apply_sigma_pos_at_self (n := n) (m := m) σ p h0 u huPos
  intro hEq
  have hcoord :
      ((permChainCell (n := n) (m := m) σ p h0) t).1 (σ u)
        =
      ((permChainCell (n := n) (m := m) σ p h0) u).1 (σ u) := by
    simpa using congrArg (fun q : GridVertex n m => q.1 (σ u)) hEq
  rw [htVal, huVal] at hcoord
  omega

theorem permChainCell_injective
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) :
    Function.Injective (permChainCell (n := n) (m := m) σ p h0) := by
  intro t u hEq
  by_cases htu : t = u
  · exact htu
  · have hvalne : t.1 ≠ u.1 := by
      intro h
      apply htu
      exact Fin.ext h
    have hlt_or_hgt : t.1 < u.1 ∨ u.1 < t.1 := lt_or_gt_of_ne hvalne
    rcases hlt_or_hgt with hlt | hgt
    · exact False.elim ((permChainCell_ne_of_lt (n := n) (m := m) σ p h0 t u hlt) hEq)
    · exact False.elim ((permChainCell_ne_of_lt (n := n) (m := m) σ p h0 u t hgt) hEq.symm)

theorem coordDiffLeOne_permChainCell
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (hn : 0 < n)
    (t u : Idx n) :
    CoordDiffLeOne
      ((permChainCell (n := n) (m := m) σ p h0) t)
      ((permChainCell (n := n) (m := m) σ p h0) u) := by
  intro i
  let k : Idx n := σ.symm i
  have hi : σ k = i := by
    simp [k]
  by_cases hk0 : k = 0
  · rw [hk0] at hi
    simpa [hi] using
      abs_sub_le_one_permChainCell_sigma0 (n := n) (m := m) σ p h0 hn t u
  · have hkpos : 0 < k.1 := by
      apply Nat.pos_of_ne_zero
      intro hkz
      apply hk0
      exact Fin.ext hkz
    simpa [hi] using
      abs_sub_le_one_permChainCell_sigma_pos (n := n) (m := m) σ p h0 k hkpos t u

/-- Local cell type for Kuhn-style constructions. -/
abbrev Cell (n m : ℕ) : Type := Idx n → GridVertex n m

/-- Mesh condition for a local cell. -/
def IsMeshCell (c : Cell n m) : Prop :=
  ∀ i i' : Idx n, CoordDiffLeOne (c i) (c i')

theorem isMeshCell_permChainCell
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (hn : 0 < n) :
    IsMeshCell (permChainCell (n := n) (m := m) σ p h0) := by
  intro i i'
  exact coordDiffLeOne_permChainCell (n := n) (m := m) σ p h0 hn i i'

/--
Star cell at source coordinate `j`:
`j`-vertex is `p`, every other vertex is one transfer from `j` to that index.
-/
def starCell (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j) : Cell n m :=
  fun i => if h : i = j then p else transferUnit p i j h hj

@[simp] theorem starCell_apply_source (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j) :
    starCell p j hj j = p := by
  simp [starCell]

@[simp] theorem starCell_apply_other (p : GridVertex n m) (j i : Idx n)
    (hj : 0 < p.1 j) (hij : i ≠ j) :
    starCell p j hj i = transferUnit p i j hij hj := by
  simp [starCell, hij]

/-- Vertices of a star cell are pairwise distinct. -/
theorem starCell_injective (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j) :
    Function.Injective (starCell p j hj) := by
  intro i i' hEq
  by_cases hij : i = j
  · subst i
    by_cases hi'j : i' = j
    · exact hi'j.symm
    · have htr : starCell p j hj i' = transferUnit p i' j hi'j hj := by
        simp [starCell, hi'j]
      have hsrc : starCell p j hj j = p := by simp [starCell]
      rw [hsrc, htr] at hEq
      have hplus : (transferUnit p i' j hi'j hj).1 i' = p.1 i' + 1 :=
        transferUnit_apply_left (n := n) (m := m) p i' j hi'j hj
      have hsame : (transferUnit p i' j hi'j hj).1 i' = p.1 i' := by
        exact congrArg (fun q : GridVertex n m => q.1 i') hEq.symm
      omega
  · by_cases hi'j : i' = j
    · subst i'
      have htr : starCell p j hj i = transferUnit p i j hij hj := by
        simp [starCell, hij]
      have hsrc : starCell p j hj j = p := by simp [starCell]
      rw [htr, hsrc] at hEq
      have hplus : (transferUnit p i j hij hj).1 i = p.1 i + 1 :=
        transferUnit_apply_left (n := n) (m := m) p i j hij hj
      have hsame : (transferUnit p i j hij hj).1 i = p.1 i := by
        exact congrArg (fun q : GridVertex n m => q.1 i) hEq
      omega
    · by_cases hii' : i = i'
      · exact hii'
      · have htri : starCell p j hj i = transferUnit p i j hij hj := by
          simp [starCell, hij]
        have htri' : starCell p j hj i' = transferUnit p i' j hi'j hj := by
          simp [starCell, hi'j]
        rw [htri, htri'] at hEq
        have hleft : (transferUnit p i j hij hj).1 i = p.1 i + 1 :=
          transferUnit_apply_left (n := n) (m := m) p i j hij hj
        have hii'ne : i ≠ i' := by exact hii'
        have hright : (transferUnit p i' j hi'j hj).1 i = p.1 i := by
          exact transferUnit_apply_other (n := n) (m := m) p i' j i hi'j hj hii'ne hij
        have hsame : (transferUnit p i j hij hj).1 i = (transferUnit p i' j hi'j hj).1 i := by
          exact congrArg (fun q : GridVertex n m => q.1 i) hEq
        rw [hleft, hright] at hsame
        omega

/--
Changing root from `p` to `transferUnit p k j` and source from `j` to `k`
represents the same star cell.
-/
theorem starCell_eq_starCell_transfer_source
    (p : GridVertex n m) (j k : Idx n)
    (hj : 0 < p.1 j) (hkj : k ≠ j) :
    let p' : GridVertex n m := transferUnit p k j hkj hj
    let hk : 0 < p'.1 k := transferUnit_pos_left (n := n) (m := m) p k j hkj hj
    starCell p j hj = starCell p' k hk := by
  funext i
  let p' : GridVertex n m := transferUnit p k j hkj hj
  let hk : 0 < p'.1 k := transferUnit_pos_left (n := n) (m := m) p k j hkj hj
  by_cases hij : i = j
  · subst i
    rw [starCell_apply_source (n := n) (m := m) p j hj]
    rw [starCell_apply_other (n := n) (m := m) p' k j hk hkj.symm]
    simpa [p'] using
      (transferUnit_cancel_opposite (n := n) (m := m) p k j hkj hj hk).symm
  · by_cases hik : i = k
    · subst i
      rw [starCell_apply_other (n := n) (m := m) p j k hj hkj]
      rw [starCell_apply_source (n := n) (m := m) p' k hk]
    · rw [starCell_apply_other (n := n) (m := m) p j i hj hij]
      rw [starCell_apply_other (n := n) (m := m) p' k i hk hik]
      simpa [p'] using
        (transferUnit_transferUnit_eq (n := n) (m := m) p i k j hij hkj hik hj hk).symm

/-- The star cell is always a mesh cell. -/
theorem isMeshCell_starCell (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j) :
    IsMeshCell (starCell p j hj) := by
  intro a b
  by_cases haj : a = j
  · subst a
    by_cases hbj : b = j
    · subst b
      intro k
      simp
    · rw [starCell_apply_source, starCell_apply_other _ _ _ hj hbj]
      exact coordDiffLeOne_transferUnit p b j hbj hj
  · by_cases hbj : b = j
    · subst b
      rw [starCell_apply_other _ _ _ hj haj, starCell_apply_source]
      exact coordDiffLeOne_symm (coordDiffLeOne_transferUnit p a j haj hj)
    · rw [starCell_apply_other _ _ _ hj haj, starCell_apply_other _ _ _ hj hbj]
      exact coordDiffLeOne_transferUnit_pair p a b j haj hbj hj

/-- Positive coordinates of a grid vertex. -/
noncomputable def positiveCoords (p : GridVertex n m) : Finset (Idx n) :=
  (Finset.univ : Finset (Idx n)).filter (fun j => 0 < p.1 j)

@[simp] theorem mem_positiveCoords_iff (p : GridVertex n m) (j : Idx n) :
    j ∈ positiveCoords p ↔ 0 < p.1 j := by
  simp [positiveCoords]

/-- Finite family of star cells rooted at a fixed grid vertex. -/
noncomputable def starCellsFrom (p : GridVertex n m) : Finset (Cell n m) := by
  classical
  exact (positiveCoords p).attach.image (fun j =>
    starCell p j.1 ((mem_positiveCoords_iff p j.1).1 j.2))

theorem mem_starCellsFrom_iff (p : GridVertex n m) (c : Cell n m) :
    c ∈ starCellsFrom p ↔
      ∃ j : Idx n, ∃ hj : 0 < p.1 j, c = starCell p j hj := by
  classical
  constructor
  · intro hc
    rcases Finset.mem_image.1 hc with ⟨j, hjmem, rfl⟩
    refine ⟨j.1, (mem_positiveCoords_iff p j.1).1 j.2, rfl⟩
  · rintro ⟨j, hj, hEq⟩
    subst hEq
    refine Finset.mem_image.2 ?_
    refine ⟨⟨j, (mem_positiveCoords_iff p j).2 hj⟩, ?_, rfl⟩
    simp

/-- Every star cell in `starCellsFrom p` is a mesh cell. -/
theorem isMeshCell_of_mem_starCellsFrom (p : GridVertex n m) {c : Cell n m}
    (hc : c ∈ starCellsFrom p) :
    IsMeshCell c := by
  rcases (mem_starCellsFrom_iff p c).1 hc with ⟨j, hj, hEq⟩
  simpa [hEq] using isMeshCell_starCell p j hj

/-- Permutation seeds with positive source coordinate at index `0`. -/
abbrev PermSeed (p : GridVertex n m) := {σ : Equiv.Perm (Idx n) // 0 < p.1 (σ 0)}

/-- Finite family of permutation-chain cells rooted at `p`. -/
noncomputable def permCellsFromRoot (p : GridVertex n m) : Finset (Cell n m) := by
  classical
  exact (Finset.univ : Finset (PermSeed (n := n) (m := m) p)).image
    (fun σ => permChainCell (n := n) (m := m) σ.1 p σ.2)

theorem mem_permCellsFromRoot_iff (p : GridVertex n m) (c : Cell n m) :
    c ∈ permCellsFromRoot (n := n) (m := m) p ↔
      ∃ σ : Equiv.Perm (Idx n), ∃ hσ : 0 < p.1 (σ 0), c = permChainCell σ p hσ := by
  classical
  unfold permCellsFromRoot
  constructor
  · intro hc
    rcases Finset.mem_image.1 hc with ⟨σ, hσmem, hEq⟩
    exact ⟨σ.1, σ.2, hEq.symm⟩
  · rintro ⟨σ, hσ, hEq⟩
    subst hEq
    refine Finset.mem_image.2 ?_
    refine ⟨⟨σ, hσ⟩, by simp, rfl⟩

/-- Every permutation-chain cell in the rooted family is mesh (for `n > 0`). -/
theorem isMeshCell_of_mem_permCellsFromRoot
    (hn : 0 < n)
    (p : GridVertex n m) {c : Cell n m}
    (hc : c ∈ permCellsFromRoot (n := n) (m := m) p) :
    IsMeshCell c := by
  rcases (mem_permCellsFromRoot_iff (n := n) (m := m) p c).1 hc with ⟨σ, hσ, hEq⟩
  simpa [hEq] using isMeshCell_permChainCell (n := n) (m := m) σ p hσ hn

/-- Permutation-chain cells assembled from a finite set of roots. -/
noncomputable def permCellsFromRoots (roots : Finset (GridVertex n m)) : Finset (Cell n m) := by
  classical
  exact roots.biUnion (permCellsFromRoot (n := n) (m := m))

theorem mem_permCellsFromRoots_iff (roots : Finset (GridVertex n m)) (c : Cell n m) :
    c ∈ permCellsFromRoots (n := n) (m := m) roots ↔
      ∃ p ∈ roots, ∃ σ : Equiv.Perm (Idx n), ∃ hσ : 0 < p.1 (σ 0), c = permChainCell σ p hσ := by
  classical
  constructor
  · intro hc
    rcases Finset.mem_biUnion.1 hc with ⟨p, hpRoots, hcP⟩
    rcases (mem_permCellsFromRoot_iff (n := n) (m := m) p c).1 hcP with ⟨σ, hσ, hEq⟩
    exact ⟨p, hpRoots, σ, hσ, hEq⟩
  · rintro ⟨p, hpRoots, σ, hσ, hEq⟩
    refine Finset.mem_biUnion.2 ?_
    refine ⟨p, hpRoots, ?_⟩
    exact (mem_permCellsFromRoot_iff (n := n) (m := m) p c).2 ⟨σ, hσ, hEq⟩

/-- Any member of `permCellsFromRoots` is a mesh cell (for `n > 0`). -/
theorem isMeshCell_of_mem_permCellsFromRoots
    (hn : 0 < n)
    (roots : Finset (GridVertex n m)) {c : Cell n m}
    (hc : c ∈ permCellsFromRoots (n := n) (m := m) roots) :
    IsMeshCell c := by
  rcases (mem_permCellsFromRoots_iff (n := n) (m := m) roots c).1 hc with
    ⟨p, hpRoots, σ, hσ, hEq⟩
  simpa [hEq] using isMeshCell_permChainCell (n := n) (m := m) σ p hσ hn

/-- Finite cell family generated from a finite set of roots. -/
noncomputable def cellsFromRoots (roots : Finset (GridVertex n m)) : Finset (Cell n m) := by
  classical
  exact roots.biUnion starCellsFrom

theorem mem_cellsFromRoots_iff (roots : Finset (GridVertex n m)) (c : Cell n m) :
    c ∈ cellsFromRoots (n := n) (m := m) roots ↔
      ∃ p ∈ roots, ∃ j : Idx n, ∃ hj : 0 < p.1 j, c = starCell p j hj := by
  classical
  constructor
  · intro hc
    rcases Finset.mem_biUnion.1 hc with ⟨p, hpRoots, hcP⟩
    rcases (mem_starCellsFrom_iff p c).1 hcP with ⟨j, hj, hEq⟩
    exact ⟨p, hpRoots, j, hj, hEq⟩
  · rintro ⟨p, hpRoots, j, hj, hEq⟩
    refine Finset.mem_biUnion.2 ?_
    refine ⟨p, hpRoots, ?_⟩
    rw [mem_starCellsFrom_iff]
    exact ⟨j, hj, hEq⟩

/-- Any member of `cellsFromRoots` is a mesh cell. -/
theorem isMeshCell_of_mem_cellsFromRoots (roots : Finset (GridVertex n m)) {c : Cell n m}
    (hc : c ∈ cellsFromRoots (n := n) (m := m) roots) :
    IsMeshCell c := by
  rcases (mem_cellsFromRoots_iff (n := n) (m := m) roots c).1 hc with
    ⟨p, hpRoots, j, hj, hEq⟩
  simpa [hEq] using isMeshCell_starCell p j hj

/-- Explicit finite root set: all grid vertices at scale `m`. -/
noncomputable def boundedVertexCodes : Finset (Idx n → Fin (m + 1)) :=
  Finset.univ

/-- Codes whose coordinate sum is exactly `m`. -/
noncomputable def exactSumCodes : Finset (Idx n → Fin (m + 1)) :=
  boundedVertexCodes (n := n) (m := m) |>.filter (fun w => (∑ i : Idx n, (w i : ℕ)) = m)

/-- Decode an exact-sum code into a grid vertex. -/
noncomputable def decodeExactSumCode
    (w : {w : Idx n → Fin (m + 1) // w ∈ exactSumCodes (n := n) (m := m)}) :
    GridVertex n m := by
  exact ⟨fun i => (w.1 i : ℕ), (Finset.mem_filter.1 w.2).2⟩

/-- Explicit finite root set: all grid vertices at scale `m`. -/
noncomputable def allGridVertices : Finset (GridVertex n m) := by
  classical
  exact (exactSumCodes (n := n) (m := m)).attach.image (decodeExactSumCode (n := n) (m := m))

/-- The explicit finite enumeration contains every grid vertex. -/
theorem mem_allGridVertices (p : GridVertex n m) :
    p ∈ allGridVertices (n := n) (m := m) := by
  classical
  have hle : ∀ i : Idx n, p.1 i ≤ m := by
    intro i
    calc
      p.1 i ≤ ∑ j : Idx n, p.1 j := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
      _ = m := p.2
  let w : Idx n → Fin (m + 1) := fun i => ⟨p.1 i, Nat.lt_succ_of_le (hle i)⟩
  have hw_mem : w ∈ exactSumCodes (n := n) (m := m) := by
    simp [exactSumCodes, boundedVertexCodes, w, p.2]
  refine Finset.mem_image.2 ?_
  refine ⟨⟨w, hw_mem⟩, ?_, ?_⟩
  · simp
  · ext i
    rfl

/--
Concrete scale-indexed cell family built from all grid roots.
This is the current concrete triangulation candidate family.
-/
noncomputable def cellsAtScale : Finset (Cell n m) :=
  cellsFromRoots (n := n) (m := m) (allGridVertices (n := n) (m := m))

/-- Permutation-chain scale family built from all grid roots. -/
noncomputable def permCellsAtScale : Finset (Cell n m) :=
  permCellsFromRoots (n := n) (m := m) (allGridVertices (n := n) (m := m))

/-- Every cell in the concrete scale family is a mesh cell. -/
theorem isMeshCell_of_mem_cellsAtScale {c : Cell n m}
    (hc : c ∈ cellsAtScale (n := n) (m := m)) :
    IsMeshCell c := by
  exact isMeshCell_of_mem_cellsFromRoots (n := n) (m := m)
    (roots := allGridVertices (n := n) (m := m)) hc

/-- Every cell in the permutation-chain scale family is mesh (for `n > 0`). -/
theorem isMeshCell_of_mem_permCellsAtScale
    (hn : 0 < n) {c : Cell n m}
    (hc : c ∈ permCellsAtScale (n := n) (m := m)) :
    IsMeshCell c := by
  exact isMeshCell_of_mem_permCellsFromRoots (n := n) (m := m) hn
    (roots := allGridVertices (n := n) (m := m)) hc

/--
Rooted star family is exactly its `cellsAtScale`-filtered version.
-/
theorem starCellsFrom_eq_filter_cellsAtScale
    (p : GridVertex n m) :
    starCellsFrom (n := n) (m := m) p
      =
    (cellsAtScale (n := n) (m := m)).filter
      (fun c => c ∈ starCellsFrom (n := n) (m := m) p) := by
  ext c
  constructor
  · intro hc
    have hcScale :
        c ∈ cellsAtScale (n := n) (m := m) := by
      rcases (mem_starCellsFrom_iff (n := n) (m := m) p c).1 hc with
        ⟨j, hj, hEq⟩
      exact (mem_cellsFromRoots_iff (n := n) (m := m)
        (allGridVertices (n := n) (m := m)) c).2
        ⟨p, mem_allGridVertices (n := n) (m := m) p, j, hj, hEq⟩
    exact Finset.mem_filter.2 ⟨hcScale, hc⟩
  · intro hc
    exact (Finset.mem_filter.1 hc).2

/--
Canonical decomposition of a cell in `permCellsAtScale` as a rooted permutation chain.
-/
theorem exists_permSeed_of_mem_permCellsAtScale
    {c : Cell n m}
    (hc : c ∈ permCellsAtScale (n := n) (m := m)) :
    ∃ p : GridVertex n m, ∃ σ : Equiv.Perm (Idx n), ∃ hσ : 0 < p.1 (σ 0),
      c = permChainCell (n := n) (m := m) σ p hσ := by
  rcases (mem_permCellsFromRoots_iff (n := n) (m := m)
      (allGridVertices (n := n) (m := m)) c).1 hc with
    ⟨p, hp, σ, hσ, hEq⟩
  exact ⟨p, σ, hσ, hEq⟩

/--
Canonical decomposition of a cell in `cellsAtScale` as a rooted star cell.
-/
theorem exists_starSeed_of_mem_cellsAtScale
    {c : Cell n m}
    (hc : c ∈ cellsAtScale (n := n) (m := m)) :
    ∃ p : GridVertex n m, ∃ j : Idx n, ∃ hj : 0 < p.1 j,
      c = starCell (n := n) (m := m) p j hj := by
  rcases (mem_cellsFromRoots_iff (n := n) (m := m)
      (allGridVertices (n := n) (m := m)) c).1 hc with
    ⟨p, hp, j, hj, hEq⟩
  exact ⟨p, j, hj, hEq⟩

/-- If `m > 0`, every grid vertex has a positive coordinate. -/
theorem exists_positiveCoord (hm : 0 < m) (p : GridVertex n m) :
    ∃ j : Idx n, 0 < p.1 j := by
  by_contra hnone
  have hzero : ∀ j : Idx n, p.1 j = 0 := by
    intro j
    by_contra hj
    exact hnone ⟨j, Nat.pos_of_ne_zero hj⟩
  have hsum0 : (∑ j : Idx n, p.1 j) = 0 := by simp [hzero]
  have : m = 0 := by simpa [p.2] using hsum0
  exact (Nat.ne_of_gt hm) this

/--
For `n > 0`, `m > 0`, there exists a grid vertex with a coordinate exactly `1`.

Construction: start from the root vertex concentrated at `0`, then transfer one
unit from coordinate `0` to coordinate `1`.
-/
theorem exists_coord_eq_one (hn : 0 < n) (hm : 0 < m) :
    ∃ p : GridVertex n m, ∃ j : Idx n, p.1 j = 1 ∧ 0 < p.1 j := by
  let i0 : Idx n := 0
  let i1 : Idx n := ⟨1, Nat.succ_lt_succ hn⟩
  have hi10 : i1 ≠ i0 := by
    intro h
    have hval : (i1 : ℕ) = (i0 : ℕ) := congrArg Fin.val h
    have : (1 : ℕ) = 0 := by simpa [i1, i0] using hval
    exact Nat.one_ne_zero this
  let p0 : GridVertex n m := by
    refine ⟨fun i => if i = i0 then m else 0, ?_⟩
    classical
    simpa [i0] using
      (Fin.sum_univ_eq_single i0 (fun b hb => by simp [hb]))
  have hp0 : 0 < p0.1 i0 := by
    dsimp [p0]
    simp [i0, hm]
  let p : GridVertex n m := transferUnit (n := n) (m := m) p0 i1 i0 hi10 hp0
  have hp_i1 : p.1 i1 = 1 := by
    dsimp [p]
    calc
      (transferUnit (n := n) (m := m) p0 i1 i0 hi10 hp0).1 i1
          = p0.1 i1 + 1 := by
              exact transferUnit_apply_left (n := n) (m := m) p0 i1 i0 hi10 hp0
      _ = 0 + 1 := by
            dsimp [p0]
            simp [i1, i0, hi10]
      _ = 1 := by simp
  refine ⟨p, i1, hp_i1, by simpa [hp_i1]⟩

/-- For `m > 0`, each rooted star family is nonempty. -/
theorem starCellsFrom_nonempty (hm : 0 < m) (p : GridVertex n m) :
    (starCellsFrom (n := n) (m := m) p).Nonempty := by
  rcases exists_positiveCoord (n := n) hm p with ⟨j, hj⟩
  refine ⟨starCell p j hj, ?_⟩
  rw [mem_starCellsFrom_iff]
  exact ⟨j, hj, rfl⟩

theorem permCellsFromRoot_nonempty (p : GridVertex n m)
    (hpos : ∃ j : Idx n, 0 < p.1 j) :
    (permCellsFromRoot (n := n) (m := m) p).Nonempty := by
  rcases hpos with ⟨j, hj⟩
  let σ : Equiv.Perm (Idx n) := Equiv.swap 0 j
  have hσ : 0 < p.1 (σ 0) := by
    simpa [σ] using hj
  refine ⟨permChainCell (n := n) (m := m) σ p hσ, ?_⟩
  exact (mem_permCellsFromRoot_iff (n := n) (m := m) p
    (permChainCell (n := n) (m := m) σ p hσ)).2 ⟨σ, hσ, rfl⟩

/-- For `m > 0`, the concrete scale cell family is nonempty. -/
theorem cellsAtScale_nonempty (hm : 0 < m) :
    (cellsAtScale (n := n) (m := m)).Nonempty := by
  let i0 : Idx n := ⟨0, Nat.succ_pos _⟩
  let p0 : GridVertex n m := by
    refine ⟨fun i => if i = i0 then m else 0, ?_⟩
    simp [i0]
  have hroots : (allGridVertices (n := n) (m := m)).Nonempty := by
    exact ⟨p0, mem_allGridVertices (n := n) (m := m) p0⟩
  rcases hroots with ⟨p, hp⟩
  rcases starCellsFrom_nonempty (n := n) (m := m) hm p with ⟨c, hc⟩
  exact ⟨c, Finset.mem_biUnion.2 ⟨p, hp, hc⟩⟩

theorem permCellsAtScale_nonempty (hm : 0 < m) :
    (permCellsAtScale (n := n) (m := m)).Nonempty := by
  let i0 : Idx n := ⟨0, Nat.succ_pos _⟩
  let p0 : GridVertex n m := by
    refine ⟨fun i => if i = i0 then m else 0, ?_⟩
    simp [i0]
  have hp0 : p0 ∈ allGridVertices (n := n) (m := m) := by
    exact mem_allGridVertices (n := n) (m := m) p0
  rcases exists_positiveCoord (n := n) hm p0 with ⟨j, hj⟩
  rcases permCellsFromRoot_nonempty (n := n) (m := m) p0 ⟨j, hj⟩ with ⟨c, hc⟩
  exact ⟨c, Finset.mem_biUnion.2 ⟨p0, hp0, hc⟩⟩

/-- Finite vertex set of a cell. -/
noncomputable def cellVertices (c : Cell n m) : Finset (GridVertex n m) := by
  classical
  exact (Finset.univ : Finset (Idx n)).image c

/-- Facet obtained by removing one vertex. -/
noncomputable def cellFacet (c : Cell n m) (i : Idx n) : Finset (GridVertex n m) := by
  classical
  exact (cellVertices (n := n) (m := m) c).erase (c i)

/--
Facet membership for an injective cell:
`v` is in facet `i` iff it is one of the cell vertices with index different from `i`.
-/
theorem mem_cellFacet_iff {c : Cell n m}
    (hc_inj : Function.Injective c)
    (i : Idx n) (v : GridVertex n m) :
    v ∈ cellFacet (n := n) (m := m) c i
      ↔ ∃ k : Idx n, k ≠ i ∧ v = c k := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_erase.1 hv with ⟨hne, hvV⟩
    rcases Finset.mem_image.1 hvV with ⟨k, hkUniv, hkEq⟩
    refine ⟨k, ?_, hkEq.symm⟩
    intro hki
    apply hne
    subst hki
    simpa using hkEq.symm
  · rintro ⟨k, hki, hkEq⟩
    refine Finset.mem_erase.2 ?_
    refine ⟨?_, ?_⟩
    · intro hEq
      apply hki
      exact hc_inj (by simpa [hkEq] using hEq)
    · refine Finset.mem_image.2 ?_
      exact ⟨k, Finset.mem_univ k, hkEq.symm⟩

/-- Facet membership characterization specialized to permutation-chain cells. -/
theorem mem_cellFacet_permChainCell_iff
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (hσ : 0 < p.1 (σ 0))
    (i : Idx n) (v : GridVertex n m) :
    v ∈ cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) σ p hσ) i
      ↔ ∃ k : Idx n, k ≠ i ∧ v = permChainCell (n := n) (m := m) σ p hσ k := by
  exact mem_cellFacet_iff (n := n) (m := m)
    (c := permChainCell (n := n) (m := m) σ p hσ)
    (permChainCell_injective (n := n) (m := m) σ p hσ)
    i v

/--
`0`-facet membership in a permutation-chain cell is exactly membership among
single-step transfers from source `σ 0` to some positive-index target.
-/
theorem mem_cellFacet_permChainCell_zero_iff_transfer
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0))
    (v : GridVertex n m) :
    v ∈ cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) σ p h0) 0
      ↔
    ∃ k : Idx n, ∃ hk : 0 < k.1,
      v =
        transferUnit (n := n) (m := m) p (σ k) (σ 0)
          (by
            intro hEq
            exact Nat.ne_of_gt hk (congrArg Fin.val (σ.injective hEq))) h0 := by
  constructor
  · intro hv
    rcases (mem_cellFacet_permChainCell_iff (n := n) (m := m) σ p h0 0 v).1 hv with
      ⟨k, hk0, hkEq⟩
    have hkpos : 0 < k.1 := by
      by_contra hkNotPos
      have hkz : k.1 = 0 := Nat.eq_zero_of_not_pos hkNotPos
      apply hk0
      exact Fin.ext hkz
    refine ⟨k, hkpos, ?_⟩
    rw [hkEq]
    simpa using permChainCell_eq_transfer_of_pos (n := n) (m := m) σ p h0 k hkpos
  · rintro ⟨k, hkpos, hkEq⟩
    have hk0 : k ≠ 0 := by
      intro h
      exact Nat.ne_of_gt hkpos (congrArg Fin.val h)
    refine (mem_cellFacet_permChainCell_iff (n := n) (m := m) σ p h0 0 v).2 ⟨k, hk0, ?_⟩
    rw [hkEq]
    symm
    simpa using permChainCell_eq_transfer_of_pos (n := n) (m := m) σ p h0 k hkpos

/--
For an injective cell, distinct indices define distinct facets.
-/
theorem cellFacet_ne_of_ne {c : Cell n m}
    (hc_inj : Function.Injective c)
    {i j : Idx n} (hij : i ≠ j) :
    cellFacet (n := n) (m := m) c i ≠ cellFacet (n := n) (m := m) c j := by
  classical
  intro hEq
  have hmem_i : c j ∈ cellFacet (n := n) (m := m) c i := by
    exact (mem_cellFacet_iff (n := n) (m := m) hc_inj i (c j)).2 ⟨j, hij.symm, rfl⟩
  have hmem_j : c j ∈ cellFacet (n := n) (m := m) c j := by simpa [hEq] using hmem_i
  have hnot : c j ∉ cellFacet (n := n) (m := m) c j := by
    simp [cellFacet]
  exact hnot hmem_j

/-- Distinct facets in a permutation-chain cell come from distinct indices. -/
theorem cellFacet_permChainCell_ne_of_ne
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (hσ : 0 < p.1 (σ 0))
    {i j : Idx n} (hij : i ≠ j) :
    cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) σ p hσ) i ≠
      cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) σ p hσ) j := by
  exact cellFacet_ne_of_ne (n := n) (m := m)
    (c := permChainCell (n := n) (m := m) σ p hσ)
    (permChainCell_injective (n := n) (m := m) σ p hσ) hij

/--
For permutation-chain cells, the root vertex `p` is not in facet `0`.
-/
theorem not_mem_cellFacet_permChainCell_zero
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (hσ : 0 < p.1 (σ 0)) :
    p ∉ cellFacet (n := n) (m := m)
      (permChainCell (n := n) (m := m) σ p hσ) 0 := by
  classical
  have hInj :
      Function.Injective (permChainCell (n := n) (m := m) σ p hσ) :=
    permChainCell_injective (n := n) (m := m) σ p hσ
  intro hpIn
  rcases (mem_cellFacet_iff (n := n) (m := m) hInj 0 p).1 hpIn with ⟨k, hk0, hkp⟩
  have h0 : (permChainCell (n := n) (m := m) σ p hσ) 0 = p := by
    simp [permChainCell, permChainVertex_zero]
  have hkEq0 : k = 0 := by
    exact hInj (by simpa [h0] using hkp.symm)
  exact hk0 hkEq0

/--
For permutation-chain cells, if `i ≠ 0`, facet `i` contains the root vertex `p`.
-/
theorem root_mem_cellFacet_permChainCell_of_ne_zero
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (hσ : 0 < p.1 (σ 0))
    (i : Idx n) (hi0 : i ≠ 0) :
    p ∈ cellFacet (n := n) (m := m)
      (permChainCell (n := n) (m := m) σ p hσ) i := by
  have hInj :
      Function.Injective (permChainCell (n := n) (m := m) σ p hσ) :=
    permChainCell_injective (n := n) (m := m) σ p hσ
  have h0 : (permChainCell (n := n) (m := m) σ p hσ) 0 = p := by
    simp [permChainCell, permChainVertex_zero]
  exact (mem_cellFacet_iff (n := n) (m := m) hInj i p).2 ⟨0, hi0.symm, h0.symm⟩

/--
Boundary-hyperface criterion for permutation-chain `0`-facets:
if `p_(σ 0) = 1`, every vertex in facet `0` has coordinate `σ 0` equal to `0`.
-/
theorem all_zeroFacet_coords_zero_permChainCell_of_coord_one
    (hn : 0 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (hσ : 0 < p.1 (σ 0))
    (hσ1 : p.1 (σ 0) = 1) :
    ∀ v ∈ cellFacet (n := n) (m := m)
      (permChainCell (n := n) (m := m) σ p hσ) 0, v.1 (σ 0) = 0 := by
  intro v hv
  rcases (mem_cellFacet_permChainCell_iff (n := n) (m := m) σ p hσ 0 v).1 hv with
    ⟨k, hk0, hkv⟩
  subst hkv
  have hk :
      ((permChainCell (n := n) (m := m) σ p hσ) k).1 (σ 0) = p.1 (σ 0) - 1 :=
    permChainCell_apply_sigma0_of_ne_zero (n := n) (m := m) hn σ p hσ k hk0
  rw [hσ1] at hk
  simpa using hk

/--
Index elimination on same-root incidences:
if a same-root permutation cell has a facet equal to a `0`-facet,
its incident facet index must be `0`.
-/
theorem facetIndex_eq_zero_of_sameRoot_eq_zeroFacet
    (σ τ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (hσ : 0 < p.1 (σ 0))
    (hτ : 0 < p.1 (τ 0))
    (i : Idx n)
    (hface :
      cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) τ p hτ) i
        =
      cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) σ p hσ) 0) :
    i = 0 := by
  by_contra hi
  have hpLeft :
      p ∈ cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) τ p hτ) i :=
    root_mem_cellFacet_permChainCell_of_ne_zero (n := n) (m := m) τ p hτ i hi
  have hpRight :
      p ∈ cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) σ p hσ) 0 := by
    simpa [hface] using hpLeft
  exact (not_mem_cellFacet_permChainCell_zero (n := n) (m := m) σ p hσ) hpRight

/--
For `n > 1`, if we shift permutation order by `finRotate (n+1)` and re-root at
the original chain's `t = 1` vertex, then the shifted facet removing `last`
equals the original facet removing `0`.
-/
theorem cellFacet_permChainCell_shifted_last_eq_original_zero
    (h1n : 1 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) :
    let hn : 0 < n := Nat.lt_trans Nat.zero_lt_one h1n
    let t1 : Idx n := ⟨1, Nat.succ_lt_succ hn⟩
    let q1 : GridVertex n m := (permChainCell (n := n) (m := m) σ p h0) t1
    let hq1 :
      0 < q1.1 (permStepSource (n := n) (σ * finRotate (n + 1)) ⟨0, hn⟩) :=
        permChainCell_pos_at_shiftedSource_zero (n := n) (m := m) hn σ p h0
    cellFacet (n := n) (m := m)
        (permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1)
        ⟨n, Nat.lt_succ_self n⟩
      =
    cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) σ p h0) 0 := by
  classical
  let hn : 0 < n := Nat.lt_trans Nat.zero_lt_one h1n
  let t1 : Idx n := ⟨1, Nat.succ_lt_succ hn⟩
  let q1 : GridVertex n m := (permChainCell (n := n) (m := m) σ p h0) t1
  let hq1 :
      0 < q1.1 (permStepSource (n := n) (σ * finRotate (n + 1)) ⟨0, hn⟩) :=
    permChainCell_pos_at_shiftedSource_zero (n := n) (m := m) hn σ p h0
  let cS : Cell n m := permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1
  let cO : Cell n m := permChainCell (n := n) (m := m) σ p h0
  have hInjS : Function.Injective cS := by
    exact permChainCell_injective (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1
  have hInjO : Function.Injective cO := by
    exact permChainCell_injective (n := n) (m := m) σ p h0
  ext v
  constructor
  · intro hv
    rcases (mem_cellFacet_iff (n := n) (m := m) hInjS ⟨n, Nat.lt_succ_self n⟩ v).1 hv with
      ⟨k, hkNe, hkEq⟩
    have hklt : k.1 < n := by
      have hkneVal : k.1 ≠ n := by
        intro hkn
        apply hkNe
        exact Fin.ext hkn
      omega
    let kFin : Fin n := ⟨k.1, hklt⟩
    have hshift :
        cS ⟨kFin.1, Nat.lt_succ_of_lt kFin.2⟩ = cO ⟨kFin.1 + 1, Nat.succ_lt_succ kFin.2⟩ := by
      simpa [cS, cO, q1, hq1] using
        permChainCell_shifted_eq_original_succ_idx (n := n) (m := m) h1n σ p h0 kFin
    have hkCast : (⟨kFin.1, Nat.lt_succ_of_lt kFin.2⟩ : Idx n) = k := by
      apply Fin.ext
      simp [kFin]
    have hvEqO : v = cO ⟨kFin.1 + 1, Nat.succ_lt_succ kFin.2⟩ := by
      calc
        v = cS k := hkEq
        _ = cS ⟨kFin.1, Nat.lt_succ_of_lt kFin.2⟩ := by simpa [hkCast]
        _ = cO ⟨kFin.1 + 1, Nat.succ_lt_succ kFin.2⟩ := hshift
    have hne0 : (⟨kFin.1 + 1, Nat.succ_lt_succ kFin.2⟩ : Idx n) ≠ 0 := by
      intro h
      have : kFin.1 + 1 = 0 := congrArg Fin.val h
      omega
    exact (mem_cellFacet_iff (n := n) (m := m) hInjO 0 v).2
      ⟨⟨kFin.1 + 1, Nat.succ_lt_succ kFin.2⟩, hne0, hvEqO⟩
  · intro hv
    rcases (mem_cellFacet_iff (n := n) (m := m) hInjO 0 v).1 hv with ⟨j, hjNe, hjEq⟩
    have hjPos : 0 < j.1 := by
      exact Nat.pos_of_ne_zero (by
        intro hj0
        apply hjNe
        exact Fin.ext hj0)
    let kFin : Fin n := ⟨j.1 - 1, by omega⟩
    let kIdx : Idx n := ⟨kFin.1, Nat.lt_succ_of_lt kFin.2⟩
    have hshift :
        cS kIdx = cO ⟨kFin.1 + 1, Nat.succ_lt_succ kFin.2⟩ := by
      simpa [cS, cO, q1, hq1, kIdx] using
        permChainCell_shifted_eq_original_succ_idx (n := n) (m := m) h1n σ p h0 kFin
    have hkj : (⟨kFin.1 + 1, Nat.succ_lt_succ kFin.2⟩ : Idx n) = j := by
      apply Fin.ext
      dsimp [kFin]
      omega
    have hvEqS : v = cS kIdx := by
      calc
        v = cO j := hjEq
        _ = cO ⟨kFin.1 + 1, Nat.succ_lt_succ kFin.2⟩ := by simpa [hkj]
        _ = cS kIdx := by simpa [hshift] using hshift.symm
    have hkNeLast : kIdx ≠ ⟨n, Nat.lt_succ_self n⟩ := by
      intro h
      have : kFin.1 = n := congrArg Fin.val h
      have : ¬ (kFin.1 < n) := by omega
      exact this kFin.2
    exact (mem_cellFacet_iff (n := n) (m := m) hInjS ⟨n, Nat.lt_succ_self n⟩ v).2
      ⟨kIdx, hkNeLast, hvEqS⟩

/--
Concrete shared-facet witness in `permCellsAtScale`:
for any rooted permutation cell `c₁ = permChainCell σ p h0` with `n > 1`,
the shifted/re-rooted cell `c₂` lies in the same scale family and shares
`c₁`'s `0`-facet (equal to `c₂`'s `last`-facet).
-/
theorem exists_sharedFacet_pair_in_permCellsAtScale
    (h1n : 1 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) :
    ∃ c₁ c₂ : Cell n m, ∃ face : Finset (GridVertex n m),
      c₁ ∈ permCellsAtScale (n := n) (m := m) ∧
      c₂ ∈ permCellsAtScale (n := n) (m := m) ∧
      c₁ ≠ c₂ ∧
      cellFacet (n := n) (m := m) c₁ 0 = face ∧
      cellFacet (n := n) (m := m) c₂ ⟨n, Nat.lt_succ_self n⟩ = face := by
  let hn : 0 < n := Nat.lt_trans Nat.zero_lt_one h1n
  let t1 : Idx n := ⟨1, Nat.succ_lt_succ hn⟩
  let c₁ : Cell n m := permChainCell (n := n) (m := m) σ p h0
  let q1 : GridVertex n m := c₁ t1
  let hq1 :
      0 < q1.1 (permStepSource (n := n) (σ * finRotate (n + 1)) ⟨0, hn⟩) :=
    permChainCell_pos_at_shiftedSource_zero (n := n) (m := m) hn σ p h0
  let c₂ : Cell n m := permChainCell (n := n) (m := m) (σ * finRotate (n + 1)) q1 hq1
  let face : Finset (GridVertex n m) := cellFacet (n := n) (m := m) c₁ 0
  have hc₁mem : c₁ ∈ permCellsAtScale (n := n) (m := m) := by
    exact (mem_permCellsFromRoots_iff (n := n) (m := m)
      (allGridVertices (n := n) (m := m)) c₁).2
      ⟨p, mem_allGridVertices (n := n) (m := m) p, σ, h0, rfl⟩
  have hq1mem : q1 ∈ allGridVertices (n := n) (m := m) := by
    exact mem_allGridVertices (n := n) (m := m) q1
  have hc₂mem : c₂ ∈ permCellsAtScale (n := n) (m := m) := by
    exact (mem_permCellsFromRoots_iff (n := n) (m := m)
      (allGridVertices (n := n) (m := m)) c₂).2
      ⟨q1, hq1mem, (σ * finRotate (n + 1)), hq1, rfl⟩
  have hfacetEq :
      cellFacet (n := n) (m := m) c₂ ⟨n, Nat.lt_succ_self n⟩
        = cellFacet (n := n) (m := m) c₁ 0 := by
    simpa [c₁, c₂, q1, hq1] using
      cellFacet_permChainCell_shifted_last_eq_original_zero (n := n) (m := m) h1n σ p h0
  have hc₁inj : Function.Injective c₁ := by
    simpa [c₁] using permChainCell_injective (n := n) (m := m) σ p h0
  have hlastNe0 : (⟨n, Nat.lt_succ_self n⟩ : Idx n) ≠ 0 := by
    intro h
    have : n = 0 := congrArg Fin.val h
    omega
  have hc₁facetNe :
      cellFacet (n := n) (m := m) c₁ ⟨n, Nat.lt_succ_self n⟩ ≠
        cellFacet (n := n) (m := m) c₁ 0 := by
    exact cellFacet_ne_of_ne (n := n) (m := m) hc₁inj hlastNe0
  have hc₁ne₂ : c₁ ≠ c₂ := by
    intro hEq
    have hfacetLastEq :
        cellFacet (n := n) (m := m) c₁ ⟨n, Nat.lt_succ_self n⟩ =
          cellFacet (n := n) (m := m) c₁ 0 := by
      calc
        cellFacet (n := n) (m := m) c₁ ⟨n, Nat.lt_succ_self n⟩
            = cellFacet (n := n) (m := m) c₂ ⟨n, Nat.lt_succ_self n⟩ := by simpa [hEq]
        _ = cellFacet (n := n) (m := m) c₁ 0 := hfacetEq
    exact hc₁facetNe hfacetLastEq
  refine ⟨c₁, c₂, face, hc₁mem, hc₂mem, hc₁ne₂, rfl, ?_⟩
  simpa [face] using hfacetEq

@[simp] theorem mem_cellVertices_starCell_source (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j) :
    p ∈ cellVertices (n := n) (m := m) (starCell p j hj) := by
  classical
  refine Finset.mem_image.2 ?_
  exact ⟨j, Finset.mem_univ j, by simp [starCell]⟩

@[simp] theorem mem_cellVertices_starCell_transfer (p : GridVertex n m) (j i : Idx n)
    (hj : 0 < p.1 j) (hij : i ≠ j) :
    transferUnit p i j hij hj ∈ cellVertices (n := n) (m := m) (starCell p j hj) := by
  classical
  refine Finset.mem_image.2 ?_
  exact ⟨i, Finset.mem_univ i, by simp [starCell, hij]⟩

/-- Source vertex belongs to every facet except the one removing the source index. -/
theorem source_mem_cellFacet_starCell_of_ne (p : GridVertex n m) (j i : Idx n)
    (hj : 0 < p.1 j) (hij : i ≠ j) :
    p ∈ cellFacet (n := n) (m := m) (starCell p j hj) i := by
  classical
  refine Finset.mem_erase.2 ?_
  refine ⟨?_, mem_cellVertices_starCell_source (n := n) (m := m) p j hj⟩
  intro hEq
  have : starCell p j hj j = starCell p j hj i := by
    simpa [starCell] using hEq
  have htr : starCell p j hj i = transferUnit p i j hij hj := by simp [starCell, hij]
  have hsrc : starCell p j hj j = p := by simp [starCell]
  rw [htr, hsrc] at this
  have hplus : (transferUnit p i j hij hj).1 i = p.1 i + 1 :=
    transferUnit_apply_left (n := n) (m := m) p i j hij hj
  have hsame : (transferUnit p i j hij hj).1 i = p.1 i := by
    exact congrArg (fun q : GridVertex n m => q.1 i) this.symm
  omega

/--
A transfer vertex with index `k` belongs to a facet removing `i`,
whenever `k ≠ j` and `k ≠ i`.
-/
theorem transfer_mem_cellFacet_starCell_of_ne (p : GridVertex n m) (j i k : Idx n)
    (hj : 0 < p.1 j) (hkj : k ≠ j) (hki : k ≠ i) :
    transferUnit p k j hkj hj ∈ cellFacet (n := n) (m := m) (starCell p j hj) i := by
  classical
  refine Finset.mem_erase.2 ?_
  have hmemV :
      transferUnit p k j hkj hj ∈ cellVertices (n := n) (m := m) (starCell p j hj) :=
    mem_cellVertices_starCell_transfer (n := n) (m := m) p j k hj hkj
  refine ⟨?_, hmemV⟩
  intro hEq
  have hkiVal : (starCell p j hj i).1 k = p.1 k := by
    by_cases hij : i = j
    · subst hij
      simp [starCell]
    · simp [starCell, hij, hki, hkj]
  have hkkVal : (transferUnit p k j hkj hj).1 k = p.1 k + 1 :=
    transferUnit_apply_left (n := n) (m := m) p k j hkj hj
  have hcoord : (transferUnit p k j hkj hj).1 k = (starCell p j hj i).1 k := by
    simpa using congrArg (fun q : GridVertex n m => q.1 k) hEq
  rw [hkiVal] at hcoord
  rw [hkkVal] at hcoord
  have : (p.1 k : ℕ) + 1 = p.1 k := by exact hcoord
  omega

/-- Exact facet membership characterization for a star cell. -/
theorem mem_cellFacet_starCell_iff (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j)
    (i : Idx n) (v : GridVertex n m) :
    v ∈ cellFacet (n := n) (m := m) (starCell p j hj) i
      ↔ ∃ k : Idx n, k ≠ i ∧ v = starCell p j hj k := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_erase.1 hv with ⟨hne, hvV⟩
    rcases Finset.mem_image.1 hvV with ⟨k, hkUniv, hkEq⟩
    refine ⟨k, ?_, hkEq.symm⟩
    intro hki
    apply hne
    subst hki
    simpa using hkEq.symm
  · rintro ⟨k, hki, hkEq⟩
    refine Finset.mem_erase.2 ?_
    refine ⟨?_, ?_⟩
    · intro hEq
      apply hki
      exact (starCell_injective (n := n) (m := m) p j hj) (by simpa [hkEq] using hEq)
    · refine Finset.mem_image.2 ?_
      exact ⟨k, Finset.mem_univ k, hkEq.symm⟩

/--
Every vertex on the source facet of `starCell p j` has `j`-coordinate `p_j - 1`.
-/
theorem coord_source_eq_sub_one_of_mem_cellFacet_starCell_source
    (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j)
    {v : GridVertex n m}
    (hv : v ∈ cellFacet (n := n) (m := m) (starCell p j hj) j) :
    v.1 j = p.1 j - 1 := by
  rcases (mem_cellFacet_starCell_iff (n := n) (m := m) p j hj j v).1 hv with
    ⟨k, hkj, hvk⟩
  subst hvk
  rw [starCell_apply_other (n := n) (m := m) p j k hj hkj]
  exact transferUnit_apply_right (n := n) (m := m) p k j hkj hj

/--
If `p_j = 1`, then every vertex of the source facet of `starCell p j`
lies on the coordinate hyperface `x_j = 0`.
-/
theorem coord_source_eq_zero_of_mem_cellFacet_starCell_source
    (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j)
    (hj1 : p.1 j = 1)
    {v : GridVertex n m}
    (hv : v ∈ cellFacet (n := n) (m := m) (starCell p j hj) j) :
    v.1 j = 0 := by
  have hvj :
      v.1 j = p.1 j - 1 :=
    coord_source_eq_sub_one_of_mem_cellFacet_starCell_source
      (n := n) (m := m) p j hj hv
  rw [hj1] at hvj
  simpa using hvj

/--
Boundary-hyperface characterization for source facets:
if `p_j = 1`, every source-facet vertex has `j`-coordinate `0`.
-/
theorem all_sourceFacet_coords_zero_of_coord_one
    (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j)
    (hj1 : p.1 j = 1) :
    ∀ v ∈ cellFacet (n := n) (m := m) (starCell p j hj) j, v.1 j = 0 := by
  intro v hv
  exact coord_source_eq_zero_of_mem_cellFacet_starCell_source
    (n := n) (m := m) p j hj hj1 hv

/--
Concrete adjacency identity:
for `k ≠ j`, the `j`-facet of `starCell p j` equals the `j`-facet of the
neighboring star cell rooted at `transferUnit p k j`.
-/
theorem cellFacet_starCell_source_eq_transfer
    (p : GridVertex n m) (j k : Idx n)
    (hj : 0 < p.1 j) (hkj : k ≠ j) :
    cellFacet (n := n) (m := m) (starCell p j hj) j =
      cellFacet (n := n) (m := m)
        (starCell (transferUnit p k j hkj hj) k
          (transferUnit_pos_left (n := n) (m := m) p k j hkj hj)) j := by
  classical
  let p' : GridVertex n m := transferUnit p k j hkj hj
  let hk : 0 < p'.1 k := by
    dsimp [p']
    exact transferUnit_pos_left (n := n) (m := m) p k j hkj hj
  ext v
  constructor
  · intro hv
    rcases (mem_cellFacet_starCell_iff (n := n) (m := m) p j hj j v).1 hv with ⟨i, hij, hvi⟩
    by_cases hik : i = k
    · have hviK : v = starCell p j hj k := by simpa [hik] using hvi
      have hvk : v = starCell p' k hk k := by
        calc
          v = starCell p j hj k := hviK
          _ = transferUnit p k j hkj hj := by
                exact starCell_apply_other (n := n) (m := m) p j k hj hkj
          _ = p' := by simp [p']
          _ = starCell p' k hk k := by
                exact (starCell_apply_source (n := n) (m := m) p' k hk).symm
      exact (mem_cellFacet_starCell_iff (n := n) (m := m) p' k hk j v).2 ⟨k, hkj, hvk⟩
    · have hcomm :
          transferUnit p' i k hik hk = transferUnit p i j hij hj := by
        simpa [p'] using
          transferUnit_transferUnit_eq (n := n) (m := m) p i k j hij hkj hik hj hk
      have hstar : starCell p' k hk i = starCell p j hj i := by
        simpa [starCell, hij, hik] using hcomm
      have hvi' : v = starCell p' k hk i := by simpa [hstar] using hvi
      exact (mem_cellFacet_starCell_iff (n := n) (m := m) p' k hk j v).2 ⟨i, hij, hvi'⟩
  · intro hv
    rcases (mem_cellFacet_starCell_iff (n := n) (m := m) p' k hk j v).1 hv with ⟨i, hij, hvi⟩
    by_cases hik : i = k
    · have hviK : v = starCell p' k hk k := by simpa [hik] using hvi
      have hvk : v = starCell p j hj k := by
        calc
          v = starCell p' k hk k := hviK
          _ = p' := by exact starCell_apply_source (n := n) (m := m) p' k hk
          _ = transferUnit p k j hkj hj := by simp [p']
          _ = starCell p j hj k := by
                exact (starCell_apply_other (n := n) (m := m) p j k hj hkj).symm
      exact (mem_cellFacet_starCell_iff (n := n) (m := m) p j hj j v).2 ⟨k, hkj, hvk⟩
    · have hcomm :
          transferUnit p' i k hik hk = transferUnit p i j hij hj := by
        simpa [p'] using
          transferUnit_transferUnit_eq (n := n) (m := m) p i k j hij hkj hik hj hk
      have hstar : starCell p j hj i = starCell p' k hk i := by
        simpa [starCell, hij, hik] using hcomm.symm
      have hvi' : v = starCell p j hj i := by simpa [hstar] using hvi
      exact (mem_cellFacet_starCell_iff (n := n) (m := m) p j hj j v).2 ⟨i, hij, hvi'⟩

/-- A source facet never contains its source vertex. -/
theorem not_mem_cellFacet_starCell_source (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j) :
    p ∉ cellFacet (n := n) (m := m) (starCell p j hj) j := by
  classical
  intro hp
  rcases Finset.mem_erase.1 hp with ⟨hne, hpV⟩
  exact hne (starCell_apply_source (n := n) (m := m) p j hj).symm

/--
If two source facets at the same root are equal, their source indices are equal.
-/
theorem sourceFacet_eq_imp_eq_source
    (p : GridVertex n m) (j j' : Idx n)
    (hj : 0 < p.1 j) (hj' : 0 < p.1 j')
    (hface :
      cellFacet (n := n) (m := m) (starCell p j hj) j =
        cellFacet (n := n) (m := m) (starCell p j' hj') j') :
    j = j' := by
  by_contra hne
  have hne' : j' ≠ j := by
    intro h
    exact hne h.symm
  have hmemR :
      transferUnit p j j' hne hj' ∈
        cellFacet (n := n) (m := m) (starCell p j' hj') j' := by
    exact transfer_mem_cellFacet_starCell_of_ne (n := n) (m := m)
      p j' j' j hj' hne (by simpa using hne)
  have hmemL :
      transferUnit p j j' hne hj' ∈
        cellFacet (n := n) (m := m) (starCell p j hj) j := by
    simpa [hface] using hmemR
  rcases (mem_cellFacet_starCell_iff (n := n) (m := m) p j hj j
      (transferUnit p j j' hne hj')).1 hmemL with ⟨k, hkj, hkEq⟩
  have hjCoordL : (transferUnit p j j' hne hj').1 j = p.1 j + 1 :=
    transferUnit_apply_left (n := n) (m := m) p j j' hne hj'
  have hjCoordR : (starCell p j hj k).1 j = p.1 j - 1 := by
    have hneqkj : k ≠ j := hkj
    rw [starCell_apply_other (n := n) (m := m) p j k hj hneqkj]
    exact transferUnit_apply_right (n := n) (m := m) p k j hneqkj hj
  have hcoord : (transferUnit p j j' hne hj').1 j = (starCell p j hj k).1 j := by
    exact congrArg (fun q : GridVertex n m => q.1 j) hkEq
  rw [hjCoordL, hjCoordR] at hcoord
  omega

/--
Inside `starCellsFrom p`, a fixed source facet is incident to at most one cell.
-/
theorem unique_sourceFacet_incidence_in_starCellsFrom
    (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j)
    {c : Cell n m}
    (hc : c ∈ starCellsFrom (n := n) (m := m) p)
    (hinc :
      ∃ i : Idx n,
        cellFacet (n := n) (m := m) c i =
          cellFacet (n := n) (m := m) (starCell p j hj) j) :
    c = starCell p j hj := by
  rcases (mem_starCellsFrom_iff (n := n) (m := m) p c).1 hc with ⟨j', hj', rfl⟩
  rcases hinc with ⟨i, hi⟩
  have hiEq : i = j' := by
    by_contra hne
    have hpIn :
        p ∈ cellFacet (n := n) (m := m) (starCell p j' hj') i := by
      exact source_mem_cellFacet_starCell_of_ne (n := n) (m := m) p j' i hj' hne
    have hpTarget : p ∈ cellFacet (n := n) (m := m) (starCell p j hj) j := by
      simpa [hi] using hpIn
    exact (not_mem_cellFacet_starCell_source (n := n) (m := m) p j hj) hpTarget
  subst i
  have hjEq : j' = j := by
    exact sourceFacet_eq_imp_eq_source (n := n) (m := m) p j' j hj' hj hi
  subst hjEq
  cases Subsingleton.elim hj' hj
  rfl

/-- Incidence relation: a face is a facet of a cell. -/
def FaceIncidentByFacet (c : Cell n m) (face : Finset (GridVertex n m)) : Prop :=
  ∃ i : Idx n, cellFacet (n := n) (m := m) c i = face

/--
Canonical decomposition of an incidence in `permCellsAtScale`:
any incident pair `(c, face)` comes from a rooted permutation chain and a facet index.
-/
theorem exists_permSeed_facetIndex_of_faceIncident_mem_permCellsAtScale
    {c : Cell n m} {face : Finset (GridVertex n m)}
    (hc : c ∈ permCellsAtScale (n := n) (m := m))
    (hinc : FaceIncidentByFacet (n := n) (m := m) c face) :
    ∃ p : GridVertex n m, ∃ σ : Equiv.Perm (Idx n), ∃ hσ : 0 < p.1 (σ 0),
      ∃ i : Idx n,
        c = permChainCell (n := n) (m := m) σ p hσ ∧
        cellFacet (n := n) (m := m)
          (permChainCell (n := n) (m := m) σ p hσ) i = face := by
  rcases exists_permSeed_of_mem_permCellsAtScale (n := n) (m := m) hc with
    ⟨p, σ, hσ, hEq⟩
  rcases hinc with ⟨i, hi⟩
  refine ⟨p, σ, hσ, i, hEq, ?_⟩
  simpa [hEq] using hi

/--
Canonical decomposition of an incidence in `cellsAtScale`:
any incident pair `(c, face)` comes from a rooted star cell and a facet index.
-/
theorem exists_starSeed_facetIndex_of_faceIncident_mem_cellsAtScale
    {c : Cell n m} {face : Finset (GridVertex n m)}
    (hc : c ∈ cellsAtScale (n := n) (m := m))
    (hinc : FaceIncidentByFacet (n := n) (m := m) c face) :
    ∃ p : GridVertex n m, ∃ j : Idx n, ∃ hj : 0 < p.1 j, ∃ i : Idx n,
      c = starCell (n := n) (m := m) p j hj ∧
      cellFacet (n := n) (m := m)
        (starCell (n := n) (m := m) p j hj) i = face := by
  rcases exists_starSeed_of_mem_cellsAtScale (n := n) (m := m) hc with
    ⟨p, j, hj, hEq⟩
  rcases hinc with ⟨i, hi⟩
  refine ⟨p, j, hj, i, hEq, ?_⟩
  simpa [hEq] using hi

/--
Same-root incidence normalization at a `0`-facet:
if `c ∈ permCellsFromRoot p` is incident to the `0`-facet of `permChainCell σ p hσ`,
then `c` is itself a permutation-chain cell from root `p` whose incident index is `0`.
-/
theorem sameRoot_incident_zeroFacet_normalForm
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (hσ : 0 < p.1 (σ 0))
    {c : Cell n m}
    (hcRoot : c ∈ permCellsFromRoot (n := n) (m := m) p)
    (hinc :
      FaceIncidentByFacet (n := n) (m := m) c
        (cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) σ p hσ) 0)) :
    ∃ τ : Equiv.Perm (Idx n), ∃ hτ : 0 < p.1 (τ 0),
      c = permChainCell (n := n) (m := m) τ p hτ ∧
      cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) τ p hτ) 0
        =
      cellFacet (n := n) (m := m) (permChainCell (n := n) (m := m) σ p hσ) 0 := by
  rcases (mem_permCellsFromRoot_iff (n := n) (m := m) p c).1 hcRoot with
    ⟨τ, hτ, hEq⟩
  rcases hinc with ⟨i, hi⟩
  have hIdx0 : i = 0 := by
    exact facetIndex_eq_zero_of_sameRoot_eq_zeroFacet (n := n) (m := m)
      σ τ p hσ hτ i (by simpa [hEq] using hi)
  refine ⟨τ, hτ, hEq, ?_⟩
  simpa [hEq, hIdx0] using hi

/-- Canonical source-facet incidence witness for a star cell. -/
theorem faceIncident_sourceFacet_starCell
    (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j) :
    FaceIncidentByFacet (n := n) (m := m)
      (starCell p j hj)
      (cellFacet (n := n) (m := m) (starCell p j hj) j) := by
  exact ⟨j, rfl⟩

/--
Inside `starCellsFrom p`, source-facet incidence to `starCell p j hj` is unique.
-/
theorem unique_sourceFacet_faceIncident_in_starCellsFrom
    (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j)
    {c : Cell n m}
    (hc : c ∈ starCellsFrom (n := n) (m := m) p)
    (hinc :
      FaceIncidentByFacet (n := n) (m := m) c
        (cellFacet (n := n) (m := m) (starCell p j hj) j)) :
    c = starCell p j hj := by
  exact unique_sourceFacet_incidence_in_starCellsFrom (n := n) (m := m) p j hj hc hinc

/--
For rooted star families, each source facet has an explicit unique incidence witness.
-/
theorem sourceFacet_uniqueWitness_starCellsFrom
    (p : GridVertex n m) (j : Idx n) (hj : 0 < p.1 j) :
    ∃ c₀, c₀ ∈ starCellsFrom (n := n) (m := m) p ∧
      FaceIncidentByFacet (n := n) (m := m) c₀
        (cellFacet (n := n) (m := m) (starCell p j hj) j) ∧
      (∀ c ∈ starCellsFrom (n := n) (m := m) p,
        FaceIncidentByFacet (n := n) (m := m) c
          (cellFacet (n := n) (m := m) (starCell p j hj) j) → c = c₀) := by
  refine ⟨starCell p j hj, ?_, ?_, ?_⟩
  · rw [mem_starCellsFrom_iff]
    exact ⟨j, hj, rfl⟩
  · exact faceIncident_sourceFacet_starCell (n := n) (m := m) p j hj
  · intro c hc hinc
    exact unique_sourceFacet_faceIncident_in_starCellsFrom (n := n) (m := m) p j hj hc hinc

/--
Rooted boundary-style characterization lifted to `cellsAtScale`:
the marked source facet of `starCell p j hj` has a unique witness among cells
coming from the same root `p`, and this witness is present in `cellsAtScale`
whenever `p` is an enumerated grid root.
-/
theorem rooted_sourceFacet_uniqueWitness_in_cellsAtScale
    (p : GridVertex n m) (hp : p ∈ allGridVertices (n := n) (m := m))
    (j : Idx n) (hj : 0 < p.1 j) :
    ∃ c₀, c₀ ∈ cellsAtScale (n := n) (m := m) ∧
      FaceIncidentByFacet (n := n) (m := m) c₀
        (cellFacet (n := n) (m := m) (starCell p j hj) j) ∧
      (∀ c ∈ cellsAtScale (n := n) (m := m), c ∈ starCellsFrom (n := n) (m := m) p →
        FaceIncidentByFacet (n := n) (m := m) c
          (cellFacet (n := n) (m := m) (starCell p j hj) j) → c = c₀) := by
  refine ⟨starCell p j hj, ?_, ?_, ?_⟩
  · exact (mem_cellsFromRoots_iff (n := n) (m := m)
      (allGridVertices (n := n) (m := m)) (starCell p j hj)).2
      ⟨p, hp, j, hj, rfl⟩
  · exact faceIncident_sourceFacet_starCell (n := n) (m := m) p j hj
  · intro c hcScale hcRoot hinc
    exact unique_sourceFacet_faceIncident_in_starCellsFrom (n := n) (m := m) p j hj hcRoot hinc

/--
Concrete boundary-style witness extraction at a positive scale:
there exists a rooted source facet in `cellsAtScale` with a unique rooted incidence witness.
-/
theorem exists_rootedBoundaryWitness_cellsAtScale (hm : 0 < m) :
    ∃ p : GridVertex n m, ∃ hp : p ∈ allGridVertices (n := n) (m := m),
      ∃ j : Idx n, ∃ hj : 0 < p.1 j,
        ∃ c₀, c₀ ∈ cellsAtScale (n := n) (m := m) ∧
          FaceIncidentByFacet (n := n) (m := m) c₀
            (cellFacet (n := n) (m := m) (starCell p j hj) j) ∧
          (∀ c ∈ cellsAtScale (n := n) (m := m), c ∈ starCellsFrom (n := n) (m := m) p →
            FaceIncidentByFacet (n := n) (m := m) c
              (cellFacet (n := n) (m := m) (starCell p j hj) j) → c = c₀) := by
  let i0 : Idx n := ⟨0, Nat.succ_pos _⟩
  let p0 : GridVertex n m := by
    refine ⟨fun i => if i = i0 then m else 0, ?_⟩
    simp [i0]
  have hp0 : p0 ∈ allGridVertices (n := n) (m := m) := mem_allGridVertices (n := n) (m := m) p0
  rcases exists_positiveCoord (n := n) hm p0 with ⟨j, hj⟩
  rcases rooted_sourceFacet_uniqueWitness_in_cellsAtScale
      (n := n) (m := m) p0 hp0 j hj with ⟨c₀, hc₀, hI₀, huniq⟩
  exact ⟨p0, hp0, j, hj, c₀, hc₀, hI₀, huniq⟩

/-- Facet family generated by a finite set of cells. -/
noncomputable def facetFamily (cells : Finset (Cell n m)) : Finset (Finset (GridVertex n m)) := by
  classical
  exact cells.biUnion (fun c =>
    (Finset.univ : Finset (Idx n)).image (fun i => cellFacet (n := n) (m := m) c i))

theorem mem_facetFamily_iff (cells : Finset (Cell n m)) (face : Finset (GridVertex n m)) :
    face ∈ facetFamily (n := n) (m := m) cells
      ↔ ∃ c ∈ cells, ∃ i : Idx n, cellFacet (n := n) (m := m) c i = face := by
  classical
  constructor
  · intro hface
    rcases Finset.mem_biUnion.1 hface with ⟨c, hc, hmem⟩
    rcases Finset.mem_image.1 hmem with ⟨i, hi, hEq⟩
    exact ⟨c, hc, i, hEq⟩
  · rintro ⟨c, hc, i, hEq⟩
    refine Finset.mem_biUnion.2 ?_
    refine ⟨c, hc, ?_⟩
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, hEq⟩

theorem faceIncidentByFacet_of_mem_facetFamily
    {cells : Finset (Cell n m)} {face : Finset (GridVertex n m)}
    (hface : face ∈ facetFamily (n := n) (m := m) cells) :
    ∃ c ∈ cells, FaceIncidentByFacet (n := n) (m := m) c face := by
  rcases (mem_facetFamily_iff (n := n) (m := m) cells face).1 hface with ⟨c, hc, i, hEq⟩
  exact ⟨c, hc, ⟨i, hEq⟩⟩

/--
Incidence-form packaging of the shared-facet permutation witness:
for `n > 1`, each rooted permutation chain cell produces a second distinct cell
in `permCellsAtScale` sharing one facet, with explicit incidence witnesses.
-/
theorem exists_twoIncidence_witness_in_permCellsAtScale
    (h1n : 1 < n)
    (σ : Equiv.Perm (Idx n))
    (p : GridVertex n m)
    (h0 : 0 < p.1 (σ 0)) :
    ∃ c₁ c₂ : Cell n m, ∃ face : Finset (GridVertex n m),
      c₁ ∈ permCellsAtScale (n := n) (m := m) ∧
      c₂ ∈ permCellsAtScale (n := n) (m := m) ∧
      c₁ ≠ c₂ ∧
      FaceIncidentByFacet (n := n) (m := m) c₁ face ∧
      FaceIncidentByFacet (n := n) (m := m) c₂ face ∧
      face ∈ facetFamily (n := n) (m := m) (permCellsAtScale (n := n) (m := m)) := by
  rcases exists_sharedFacet_pair_in_permCellsAtScale (n := n) (m := m) h1n σ p h0 with
    ⟨c₁, c₂, face, hc₁, hc₂, hneq, hface₁, hface₂⟩
  refine ⟨c₁, c₂, face, hc₁, hc₂, hneq, ?_, ?_, ?_⟩
  · exact ⟨0, hface₁⟩
  · exact ⟨⟨n, Nat.lt_succ_self n⟩, hface₂⟩
  · exact (mem_facetFamily_iff (n := n) (m := m)
      (permCellsAtScale (n := n) (m := m)) face).2 ⟨c₁, hc₁, 0, hface₁⟩

/--
Global 2-incidence witness statement over all admissible rooted permutation seeds.
-/
theorem global_twoIncidence_witness_permCellsAtScale
    (h1n : 1 < n) :
    ∀ (p : GridVertex n m) (σ : Equiv.Perm (Idx n)),
      0 < p.1 (σ 0) →
      ∃ c₁ c₂ : Cell n m, ∃ face : Finset (GridVertex n m),
        c₁ ∈ permCellsAtScale (n := n) (m := m) ∧
        c₂ ∈ permCellsAtScale (n := n) (m := m) ∧
        c₁ ≠ c₂ ∧
        FaceIncidentByFacet (n := n) (m := m) c₁ face ∧
        FaceIncidentByFacet (n := n) (m := m) c₂ face ∧
        face ∈ facetFamily (n := n) (m := m) (permCellsAtScale (n := n) (m := m)) := by
  intro p σ h0
  exact exists_twoIncidence_witness_in_permCellsAtScale (n := n) (m := m) h1n σ p h0

/--
Scale-level assembly of the currently proved combinatorial blocks:
1. global interior-style two-incidence witnesses over permutation seeds,
2. rooted marked-facet unique-witness characterization on `cellsAtScale`.
-/
theorem scale_incidence_boundary_blocks
    (h1n : 1 < n) :
    (∀ (p : GridVertex n m) (σ : Equiv.Perm (Idx n)),
      0 < p.1 (σ 0) →
      ∃ c₁ c₂ : Cell n m, ∃ face : Finset (GridVertex n m),
        c₁ ∈ permCellsAtScale (n := n) (m := m) ∧
        c₂ ∈ permCellsAtScale (n := n) (m := m) ∧
        c₁ ≠ c₂ ∧
        FaceIncidentByFacet (n := n) (m := m) c₁ face ∧
        FaceIncidentByFacet (n := n) (m := m) c₂ face ∧
        face ∈ facetFamily (n := n) (m := m) (permCellsAtScale (n := n) (m := m))) ∧
    (∀ (p : GridVertex n m), p ∈ allGridVertices (n := n) (m := m) →
      ∀ (j : Idx n) (hj : 0 < p.1 j),
      ∃ c₀, c₀ ∈ cellsAtScale (n := n) (m := m) ∧
        FaceIncidentByFacet (n := n) (m := m) c₀
          (cellFacet (n := n) (m := m) (starCell p j hj) j) ∧
        (∀ c ∈ cellsAtScale (n := n) (m := m), c ∈ starCellsFrom (n := n) (m := m) p →
          FaceIncidentByFacet (n := n) (m := m) c
            (cellFacet (n := n) (m := m) (starCell p j hj) j) → c = c₀)) := by
  refine ⟨?_, ?_⟩
  · exact global_twoIncidence_witness_permCellsAtScale (n := n) (m := m) h1n
  · intro p hp j hj
    simpa using rooted_sourceFacet_uniqueWitness_in_cellsAtScale (n := n) (m := m) p hp j hj

/--
Final-cut local assembly at one scale (`n > 1`, `m > 0`):
global two-incidence block together with a concrete rooted boundary witness.
-/
theorem scale_incidence_boundary_blocks_concrete
    (h1n : 1 < n) (hm : 0 < m) :
    (∀ (p : GridVertex n m) (σ : Equiv.Perm (Idx n)),
      0 < p.1 (σ 0) →
      ∃ c₁ c₂ : Cell n m, ∃ face : Finset (GridVertex n m),
        c₁ ∈ permCellsAtScale (n := n) (m := m) ∧
        c₂ ∈ permCellsAtScale (n := n) (m := m) ∧
        c₁ ≠ c₂ ∧
        FaceIncidentByFacet (n := n) (m := m) c₁ face ∧
        FaceIncidentByFacet (n := n) (m := m) c₂ face ∧
        face ∈ facetFamily (n := n) (m := m) (permCellsAtScale (n := n) (m := m))) ∧
    (∃ p : GridVertex n m, ∃ hp : p ∈ allGridVertices (n := n) (m := m),
      ∃ j : Idx n, ∃ hj : 0 < p.1 j,
        ∃ c₀, c₀ ∈ cellsAtScale (n := n) (m := m) ∧
          FaceIncidentByFacet (n := n) (m := m) c₀
            (cellFacet (n := n) (m := m) (starCell p j hj) j) ∧
          (∀ c ∈ cellsAtScale (n := n) (m := m), c ∈ starCellsFrom (n := n) (m := m) p →
            FaceIncidentByFacet (n := n) (m := m) c
              (cellFacet (n := n) (m := m) (starCell p j hj) j) → c = c₀)) := by
  refine ⟨?_, ?_⟩
  · intro p σ h0
    exact global_twoIncidence_witness_permCellsAtScale (n := n) (m := m) h1n p σ h0
  · exact exists_rootedBoundaryWitness_cellsAtScale (n := n) (m := m) hm

/--
Concrete marked-facet package at scale `m > 0`:
produces a marked face in `facetFamily (cellsAtScale)` with one witness cell and
rooted uniqueness on that face.
-/
theorem exists_markedFacet_uniqueWitness_cellsAtScale (hm : 0 < m) :
    ∃ p : GridVertex n m, ∃ hp : p ∈ allGridVertices (n := n) (m := m),
      ∃ j : Idx n, ∃ hj : 0 < p.1 j,
      ∃ f0 : Finset (GridVertex n m), ∃ c₀ : Cell n m,
        c₀ ∈ cellsAtScale (n := n) (m := m) ∧
        FaceIncidentByFacet (n := n) (m := m) c₀ f0 ∧
        f0 ∈ facetFamily (n := n) (m := m) (cellsAtScale (n := n) (m := m)) ∧
        (∀ c ∈ cellsAtScale (n := n) (m := m), c ∈ starCellsFrom (n := n) (m := m) p →
          FaceIncidentByFacet (n := n) (m := m) c f0 → c = c₀) := by
  rcases exists_rootedBoundaryWitness_cellsAtScale (n := n) (m := m) hm with
    ⟨p, hp, j, hj, c₀, hc₀, hI₀, huniq⟩
  let f0 : Finset (GridVertex n m) := cellFacet (n := n) (m := m) (starCell p j hj) j
  have hf0 : f0 ∈ facetFamily (n := n) (m := m) (cellsAtScale (n := n) (m := m)) := by
    rcases hI₀ with ⟨i, hi⟩
    exact (mem_facetFamily_iff (n := n) (m := m)
      (cellsAtScale (n := n) (m := m)) f0).2 ⟨c₀, hc₀, i, hi⟩
  refine ⟨p, hp, j, hj, f0, c₀, hc₀, ?_, hf0, ?_⟩
  · simpa [f0] using hI₀
  · intro c hc hroot hinc
    exact huniq c hc hroot (by simpa [f0] using hinc)

/--
Boundary-hyperface marked-face package at scale:
for `n > 0`, `m > 0` we can choose a marked source facet with
all vertices on one coordinate hyperface (`x_j = 0`) and with
rooted unique-witness incidence in `cellsAtScale`.
-/
theorem exists_markedFacet_coordZero_uniqueWitness_cellsAtScale
    (hn : 0 < n) (hm : 0 < m) :
    ∃ p : GridVertex n m, ∃ hp : p ∈ allGridVertices (n := n) (m := m),
      ∃ j : Idx n, ∃ hj : 0 < p.1 j, p.1 j = 1 ∧
      ∃ f0 : Finset (GridVertex n m), ∃ c₀ : Cell n m,
        c₀ ∈ cellsAtScale (n := n) (m := m) ∧
        FaceIncidentByFacet (n := n) (m := m) c₀ f0 ∧
        f0 ∈ facetFamily (n := n) (m := m) (cellsAtScale (n := n) (m := m)) ∧
        (∀ v ∈ f0, v.1 j = 0) ∧
        (∀ c ∈ cellsAtScale (n := n) (m := m), c ∈ starCellsFrom (n := n) (m := m) p →
          FaceIncidentByFacet (n := n) (m := m) c f0 → c = c₀) := by
  rcases exists_coord_eq_one (n := n) (m := m) hn hm with ⟨p, j, hj1, hj⟩
  have hp : p ∈ allGridVertices (n := n) (m := m) := mem_allGridVertices (n := n) (m := m) p
  rcases rooted_sourceFacet_uniqueWitness_in_cellsAtScale
      (n := n) (m := m) p hp j hj with
    ⟨c₀, hc₀, hI₀, huniq⟩
  let f0 : Finset (GridVertex n m) := cellFacet (n := n) (m := m) (starCell p j hj) j
  have hf0 : f0 ∈ facetFamily (n := n) (m := m) (cellsAtScale (n := n) (m := m)) := by
    rcases hI₀ with ⟨i, hi⟩
    exact (mem_facetFamily_iff (n := n) (m := m)
      (cellsAtScale (n := n) (m := m)) f0).2 ⟨c₀, hc₀, i, hi⟩
  have hcoord0 : ∀ v ∈ f0, v.1 j = 0 := by
    simpa [f0] using
      (all_sourceFacet_coords_zero_of_coord_one (n := n) (m := m) p j hj hj1)
  refine ⟨p, hp, j, hj, hj1, f0, c₀, hc₀, ?_, hf0, hcoord0, ?_⟩
  · simpa [f0] using hI₀
  · intro c hc hroot hinc
    exact huniq c hc hroot (by simpa [f0] using hinc)

end GridMoves

end KuhnSubdivision

end Fixpoint
