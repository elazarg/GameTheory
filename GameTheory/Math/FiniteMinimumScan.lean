import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-! Stable finite minimum scans with explicit eligibility and comparison flags.
The executable recurrence visits indices in increasing order and retains the
earliest index when values tie. Order assumptions occur only in correctness.
-/
namespace GameTheory.Math.FiniteMinimumScan

/-- Scan the first `n` indices, retaining the earliest eligible minimum. -/
def minimumPrefix (eligible : ℕ → Bool) (lt : ℕ → ℕ → Bool) : ℕ → Option ℕ
  | 0 => none
  | n + 1 =>
    if eligible n then
      match minimumPrefix eligible lt n with
      | none => some n
      | some j => if lt n j then some n else some j
    else minimumPrefix eligible lt n

theorem minimumPrefix_none (eligible : ℕ → Bool) (lt : ℕ → ℕ → Bool) (n : ℕ) :
    minimumPrefix eligible lt n = none ↔ ∀ i < n, eligible i = false := by
  induction n with
  | zero => simp [minimumPrefix]
  | succ n ih =>
    rw [Nat.forall_lt_succ_right]
    cases he : eligible n
    · simpa [minimumPrefix, he] using ih
    · cases hs : minimumPrefix eligible lt n with
      | none => simp [minimumPrefix, he, hs]
      | some j => cases hc : lt n j <;> simp [minimumPrefix, he, hs, hc]

/-- Every selected index is eligible and lies within the scanned prefix. -/
theorem minimumPrefix_mem (eligible : ℕ → Bool) (lt : ℕ → ℕ → Bool)
    (n s : ℕ) (hs : minimumPrefix eligible lt n = some s) : s < n ∧ eligible s = true := by
  induction n generalizing s with
  | zero => simp [minimumPrefix] at hs
  | succ n ih =>
    cases he : eligible n
    · have hm := ih s (by simpa [minimumPrefix, he] using hs)
      exact ⟨by omega, hm.2⟩
    · cases hj : minimumPrefix eligible lt n with
      | none =>
        have hns : n = s := by simpa [minimumPrefix, he, hj] using hs
        subst s
        exact ⟨Nat.lt_succ_self _, he⟩
      | some j =>
        cases hc : lt n j
        · have hjs : j = s := by simpa [minimumPrefix, he, hj, hc] using hs
          subst s
          have hm := ih j hj
          exact ⟨by omega, hm.2⟩
        · have hns : n = s := by simpa [minimumPrefix, he, hj, hc] using hs
          subst s
          exact ⟨Nat.lt_succ_self _, he⟩

/-- Only eligibility and comparison values inside the scanned prefix can affect selection. -/
theorem minimumPrefix_congr (eligible eligible' : ℕ → Bool) (lt lt' : ℕ → ℕ → Bool)
    (n : ℕ) (he : ∀ i < n, eligible i = eligible' i)
    (hc : ∀ i < n, ∀ j < n, lt i j = lt' i j) :
    minimumPrefix eligible lt n = minimumPrefix eligible' lt' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun i hi => he i (by omega))
      (fun i hi j hj => hc i (by omega) j (by omega))
    simp only [minimumPrefix, he n (by omega), hp]
    cases hstate : minimumPrefix eligible' lt' n with
    | none => rfl
    | some j =>
      have hj := (minimumPrefix_mem eligible' lt' n j hstate).1
      simp only [hc n (by omega) j (by omega)]

/-- Correct comparisons on eligible indices make the selected value minimal. -/
theorem minimumPrefix_minimal {K : Type*} [LinearOrder K]
    (eligible : ℕ → Bool) (lt : ℕ → ℕ → Bool) (value : ℕ → K)
    (hcmp : ∀ i j, eligible i = true → eligible j = true →
      (lt i j = true ↔ value i < value j))
    (n s : ℕ) (hs : minimumPrefix eligible lt n = some s) :
    ∀ i < n, eligible i = true → value s ≤ value i := by
  induction n generalizing s with
  | zero => simp [minimumPrefix] at hs
  | succ n ih =>
    cases he : eligible n
    · have hs' : minimumPrefix eligible lt n = some s := by simpa [minimumPrefix, he] using hs
      intro i hi hei
      have hi' : i < n := by
        by_contra hn
        have hin : i = n := by omega
        subst i
        simp [he] at hei
      exact ih s hs' i hi' hei
    · cases hj : minimumPrefix eligible lt n with
      | none =>
        have hns : n = s := by simpa [minimumPrefix, he, hj] using hs
        subst s
        have hempty := (minimumPrefix_none eligible lt n).mp hj
        intro i hi hei
        have hin : i = n := by
          by_contra hne
          have hi' : i < n := by omega
          have := hempty i hi'
          simp [hei] at this
        subst i
        exact le_rfl
      | some j =>
        have hjmem := minimumPrefix_mem eligible lt n j hj
        cases hc : lt n j
        · have hjs : j = s := by simpa [minimumPrefix, he, hj, hc] using hs
          subst s
          have hle : value j ≤ value n := le_of_not_gt fun hn => by
            have ht := (hcmp n j he hjmem.2).mpr hn
            simp [hc] at ht
          intro i hi hei
          by_cases hin : i = n
          · subst i; exact hle
          · exact ih j hj i (by omega) hei
        · have hns : n = s := by simpa [minimumPrefix, he, hj, hc] using hs
          subst s
          have hlt := (hcmp n j he hjmem.2).mp hc
          intro i hi hei
          by_cases hin : i = n
          · subst i; exact le_rfl
          · exact hlt.le.trans (ih j hj i (by omega) hei)

end GameTheory.Math.FiniteMinimumScan
