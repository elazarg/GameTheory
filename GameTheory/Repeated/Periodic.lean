/-
# Periodic repeated paths

Exact normalized discounted values of finite cycles and their uniform
convergence to cycle averages as the discount factor tends to one, using
explicit payoff bounds and canonical list-history paths.
-/

import GameTheory.Math.FinRotation
import GameTheory.Repeated.Discounted

noncomputable section

open scoped BigOperators

namespace GameTheory

universe uι

variable {ι : Type uι}

namespace UtilityGame

/-- Average stage payoff of a nonempty finite cycle. -/
def cycleAveragePayoff (G : UtilityGame ι) {n : ℕ}
    (cycle : Fin n → Profile G.form.sig) (who : ι)
    (hcycle : ∀ t, UtilityIntegrable G.utility who
      (G.form.play (cycle t))) : ℝ :=
  (n : ℝ)⁻¹ * ∑ t : Fin n, G.stagePayoff (cycle t) who (hcycle t)

/-- A finite cycle supplies the integration certificate for every repeated
stage on its periodic path. -/
theorem periodicStageIntegrable (G : UtilityGame ι) {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G.form.sig) (who : ι)
    (hcycle : ∀ j, UtilityIntegrable G.utility who
      (G.form.play (cycle j))) :
    ∀ t, UtilityIntegrable G.utility who
      (G.form.play (G.repeatedPlay (G.periodicRepeatedProfile cycle) t)) := by
  intro t
  simpa only [G.repeatedPlay_periodicRepeatedProfile] using
    (hcycle (Fin.ofNat n t))

/-- Finite guarded cycle values supply the actual discounted-series
certificate without a separately assumed global payoff bound. -/
theorem periodicDiscountedSummable (G : UtilityGame ι)
    {n : ℕ} [NeZero n] {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (cycle : Fin n → Profile G.form.sig) (who : ι)
    (hcycle : ∀ j, UtilityIntegrable G.utility who
      (G.form.play (cycle j))) :
    Summable fun t : ℕ => discount ^ t *
      G.stagePayoff (G.repeatedPlay (G.periodicRepeatedProfile cycle) t)
        who (G.periodicStageIntegrable cycle who hcycle t) := by
  let bound := ∑ j : Fin n,
    |G.stagePayoff (cycle j) who (hcycle j)|
  apply G.summable_discounted_stagePayoff_of_abs_bound
    hdiscount0 hdiscount1 who (G.periodicStageIntegrable cycle who hcycle)
  intro t
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun j : Fin n => |G.stagePayoff (cycle j) who (hcycle j)|)
    (fun j _ => abs_nonneg _)
    (Finset.mem_univ (Fin.ofNat n t))
  simpa only [G.repeatedPlay_periodicRepeatedProfile] using hsingle

/-- Exact normalized discounted payoff of a periodic repeated profile. -/
theorem discountedPayoff_periodicRepeatedProfile_eq
    (G : UtilityGame ι) {n : ℕ} [NeZero n]
    {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (cycle : Fin n → Profile G.form.sig) (who : ι)
    (hcycle : ∀ j, UtilityIntegrable G.utility who
      (G.form.play (cycle j))) :
    G.discountedPayoff discount (G.periodicRepeatedProfile cycle)
        who (G.periodicStageIntegrable cycle who hcycle)
        (G.periodicDiscountedSummable hdiscount0 hdiscount1
          cycle who hcycle) =
      (∑ j : Fin n,
          discount ^ (j : ℕ) * G.stagePayoff (cycle j) who (hcycle j)) /
        (∑ j : Fin n, discount ^ (j : ℕ)) := by
  let profile : G.RepeatedProfile := G.periodicRepeatedProfile cycle
  let hpath : ∀ t, UtilityIntegrable G.utility who
      (G.form.play (G.repeatedPlay profile t)) :=
    G.periodicStageIntegrable cycle who hcycle
  have hs : Summable fun t : ℕ =>
      discount ^ t * G.stagePayoff (G.repeatedPlay profile t)
        who (hpath t) :=
    G.periodicDiscountedSummable hdiscount0 hdiscount1 cycle who hcycle
  have hpow : discount ^ n < 1 :=
    pow_lt_one₀ hdiscount0 hdiscount1 (NeZero.ne n)
  have hdenPos : 0 < ∑ j : Fin n, discount ^ (j : ℕ) := by
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j : Fin n => discount ^ (j : ℕ))
      (fun j _ => pow_nonneg hdiscount0 (j : ℕ))
      (Finset.mem_univ (0 : Fin n))
    exact zero_lt_one.trans_le (by simpa using hsingle)
  have hden : (∑ j : Fin n, discount ^ (j : ℕ)) ≠ 0 :=
    ne_of_gt hdenPos
  have hgeom :
      (∑ j : Fin n, discount ^ (j : ℕ)) * (1 - discount) =
        1 - discount ^ n := by
    simpa [Finset.sum_range] using
      geom_sum_mul_of_le_one hdiscount1.le n
  have hone : 1 - discount ≠ 0 := by linarith
  have hvalue (t : ℕ) :
      G.stagePayoff (G.repeatedPlay profile t) who (hpath t) =
        G.stagePayoff (cycle (Fin.ofNat n t)) who
          (hcycle (Fin.ofNat n t)) := by
    simp only [profile, G.repeatedPlay_periodicRepeatedProfile]
  have hsplit :
      (∑' t : ℕ,
          discount ^ t * G.stagePayoff (G.repeatedPlay profile t)
            who (hpath t)) =
        ∑ j : ZMod n, ∑' m : ℕ,
          discount ^ (j.val + n * m) *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
              (hcycle ⟨j.val, j.val_lt⟩) := by
    rw [Nat.sumByResidueClasses hs n]
    refine Finset.sum_congr rfl ?_
    intro j _
    apply tsum_congr
    intro m
    rw [hvalue]
    congr 1
    simp [Fin.ofNat, Nat.mod_eq_of_lt j.val_lt]
  have hinner : ∀ j : ZMod n,
      (∑' m : ℕ,
          discount ^ (j.val + n * m) *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
              (hcycle ⟨j.val, j.val_lt⟩)) =
        (discount ^ j.val *
          G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
            (hcycle ⟨j.val, j.val_lt⟩)) *
            (1 - discount ^ n)⁻¹ := by
    intro j
    calc
      (∑' m : ℕ,
          discount ^ (j.val + n * m) *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
              (hcycle ⟨j.val, j.val_lt⟩)) =
        ∑' m : ℕ,
          (discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
              (hcycle ⟨j.val, j.val_lt⟩)) *
              (discount ^ n) ^ m := by
        apply tsum_congr
        intro m
        rw [pow_add, pow_mul]
        ring
      _ = (discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
              (hcycle ⟨j.val, j.val_lt⟩)) *
          (∑' m : ℕ, (discount ^ n) ^ m) := by
        rw [tsum_mul_left]
      _ = (discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
              (hcycle ⟨j.val, j.val_lt⟩)) *
          (1 - discount ^ n)⁻¹ := by
        rw [tsum_geometric_of_lt_one (pow_nonneg hdiscount0 n) hpow]
  have hzsum :
      (∑ j : ZMod n,
          discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
              (hcycle ⟨j.val, j.val_lt⟩)) =
        ∑ j : Fin n,
          discount ^ (j : ℕ) * G.stagePayoff (cycle j) who
            (hcycle j) := by
    exact Fintype.sum_equiv (GameTheory.Math.zmodFinEquiv n)
      (fun j : ZMod n =>
        discount ^ j.val *
          G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
            (hcycle ⟨j.val, j.val_lt⟩))
      (fun j : Fin n =>
        discount ^ (j : ℕ) * G.stagePayoff (cycle j) who (hcycle j))
      (fun _ => rfl)
  calc
    G.discountedPayoff discount (G.periodicRepeatedProfile cycle)
        who hpath hs =
        (1 - discount) * (∑ j : ZMod n,
          (discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
              (hcycle ⟨j.val, j.val_lt⟩)) *
              (1 - discount ^ n)⁻¹) := by
      simp only [discountedPayoff, GameTheory.Math.normalizedDiscountedSum]
      rw [hsplit]
      congr 1
      exact Finset.sum_congr rfl fun j _ => hinner j
    _ = (1 - discount) *
        ((∑ j : ZMod n,
          discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who
              (hcycle ⟨j.val, j.val_lt⟩)) *
              (1 - discount ^ n)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (∑ j : Fin n,
          discount ^ (j : ℕ) * G.stagePayoff (cycle j) who
            (hcycle j)) /
        (∑ j : Fin n, discount ^ (j : ℕ)) := by
      rw [hzsum, ← hgeom]
      field_simp [hden, hone]

/-- A continuation of a periodic path is the discounted payoff of its rotated
cycle. -/
theorem periodicContinuationStageIntegrable (G : UtilityGame ι)
    {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G.form.sig) (start : ℕ) (who : ι)
    (hcycle : ∀ j, UtilityIntegrable G.utility who
      (G.form.play (cycle j))) :
    ∀ k, UtilityIntegrable G.utility who
      (G.form.play (cycle (Fin.ofNat n (start + k)))) :=
  fun k => hcycle (Fin.ofNat n (start + k))

theorem periodicContinuationSummable (G : UtilityGame ι)
    {n : ℕ} [NeZero n] {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (cycle : Fin n → Profile G.form.sig) (start : ℕ) (who : ι)
    (hcycle : ∀ j, UtilityIntegrable G.utility who
      (G.form.play (cycle j))) :
    Summable fun k : ℕ => discount ^ k *
      G.stagePayoff (cycle (Fin.ofNat n (start + k))) who
        (G.periodicContinuationStageIntegrable cycle start who hcycle k) := by
  let bound := ∑ j : Fin n, |G.stagePayoff (cycle j) who (hcycle j)|
  apply G.summable_discounted_continuation_of_abs_bound
    hdiscount0 hdiscount1 (fun t => cycle (Fin.ofNat n t)) start who
    (G.periodicContinuationStageIntegrable cycle start who hcycle)
  intro k
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun j : Fin n => |G.stagePayoff (cycle j) who (hcycle j)|)
    (fun j _ => abs_nonneg _)
    (Finset.mem_univ (Fin.ofNat n (start + k)))

theorem discountedContinuationPayoff_periodicPath_eq
    (G : UtilityGame ι) {n : ℕ} [NeZero n]
    {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (cycle : Fin n → Profile G.form.sig) (start : ℕ) (who : ι)
    (hcycle : ∀ j, UtilityIntegrable G.utility who
      (G.form.play (cycle j))) :
    G.discountedContinuationPayoff discount
        (fun t => cycle (Fin.ofNat n t)) start who
        (G.periodicContinuationStageIntegrable cycle start who hcycle)
        (G.periodicContinuationSummable
          hdiscount0 hdiscount1 cycle start who hcycle) =
      (∑ j : Fin n, discount ^ (j : ℕ) *
          G.stagePayoff (cycle (Fin.ofNat n (start + j))) who
            (hcycle (Fin.ofNat n (start + j)))) /
        (∑ j : Fin n, discount ^ (j : ℕ)) := by
  let rotated : Fin n → Profile G.form.sig :=
    fun j => cycle (Fin.ofNat n (start + j))
  let hrotated : ∀ j, UtilityIntegrable G.utility who
      (G.form.play (rotated j)) :=
    fun j => hcycle (Fin.ofNat n (start + j))
  have hcontinuation :
      G.discountedContinuationPayoff discount
          (fun t => cycle (Fin.ofNat n t)) start who
          (G.periodicContinuationStageIntegrable cycle start who hcycle)
          (G.periodicContinuationSummable
            hdiscount0 hdiscount1 cycle start who hcycle) =
        G.discountedPayoff discount
          (G.periodicRepeatedProfile rotated) who
          (G.periodicStageIntegrable rotated who hrotated)
          (G.periodicDiscountedSummable
            hdiscount0 hdiscount1 rotated who hrotated) := by
    simp only [discountedContinuationPayoff, discountedPayoff,
      GameTheory.Math.normalizedDiscountedSum]
    congr 1
    apply tsum_congr
    intro k
    congr 2
    unfold rotated
    ext
    simp [Fin.ofNat, Nat.add_mod]
  rw [hcontinuation]
  exact G.discountedPayoff_periodicRepeatedProfile_eq
    hdiscount0 hdiscount1 rotated who hrotated

/-- Finite discounted phase weights converge to uniform cycle weights as the
discount factor tends to one from below. -/
theorem exists_discountFactor_threshold_weighted_cycleAverage
    {n : ℕ} [NeZero n] (value : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold : ℝ, 0 ≤ threshold ∧ threshold < 1 ∧
      ∀ discount : ℝ, threshold < discount → discount < 1 →
        |(∑ j : Fin n, discount ^ (j : ℕ) * value j) /
            (∑ j : Fin n, discount ^ (j : ℕ)) -
          (n : ℝ)⁻¹ * ∑ j : Fin n, value j| < ε := by
  let weighted : ℝ → ℝ := fun discount =>
    (∑ j : Fin n, discount ^ (j : ℕ) * value j) /
      (∑ j : Fin n, discount ^ (j : ℕ))
  have hden : (∑ j : Fin n, (1 : ℝ) ^ (j : ℕ)) ≠ 0 := by
    simp [NeZero.ne n]
  have hcontinuous : ContinuousAt weighted 1 := by
    dsimp [weighted]
    apply ContinuousAt.div
    · exact (continuous_finsetSum (Finset.univ : Finset (Fin n))
        (fun j _ =>
          (continuous_id.pow (j : ℕ)).mul continuous_const)).continuousAt
    · exact (continuous_finsetSum (Finset.univ : Finset (Fin n))
        (fun j _ => continuous_id.pow (j : ℕ))).continuousAt
    · exact hden
  have hone :
      weighted 1 = (n : ℝ)⁻¹ * ∑ j : Fin n, value j := by
    dsimp [weighted]
    simp [Finset.sum_const, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne n)]
  rcases (Metric.tendsto_nhds_nhds.1 hcontinuous) ε hε with
    ⟨distance, hdistance, hnear⟩
  let radius : ℝ := min distance 1
  have hradius : 0 < radius := lt_min hdistance zero_lt_one
  have hleDistance : radius ≤ distance := min_le_left distance 1
  have hleOne : radius ≤ 1 := min_le_right distance 1
  refine ⟨1 - radius / 2, by nlinarith, by nlinarith, ?_⟩
  intro discount hdiscount hdiscount1
  have hdist : dist discount 1 < distance := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hdiscount1.le)]
    nlinarith
  have hclose := hnear hdist
  rw [Real.dist_eq] at hclose
  simpa [weighted, hone] using hclose

/-- Combine finitely many discount thresholds into one. -/
theorem exists_common_discountFactor_threshold
    {α : Type*} [Fintype α] {property : α → ℝ → Prop}
    (hproperty : ∀ a : α, ∃ threshold : ℝ,
      0 ≤ threshold ∧ threshold < 1 ∧
        ∀ discount : ℝ, threshold < discount → discount < 1 →
          property a discount) :
    ∃ threshold : ℝ, 0 ≤ threshold ∧ threshold < 1 ∧
      ∀ discount : ℝ, threshold < discount → discount < 1 →
        ∀ a : α, property a discount := by
  classical
  choose candidate hc0 hc1 hc using hproperty
  by_cases hnonempty : (Finset.univ : Finset α).Nonempty
  · let threshold : ℝ :=
      (Finset.univ : Finset α).sup' hnonempty candidate
    refine ⟨threshold, ?_, ?_, ?_⟩
    · rcases hnonempty with ⟨a, ha⟩
      exact (hc0 a).trans (Finset.le_sup' candidate ha)
    · rw [Finset.sup'_lt_iff]
      intro a _
      exact hc1 a
    · intro discount hdiscount hdiscount1 a
      exact hc a discount
        ((Finset.le_sup' candidate (Finset.mem_univ a)).trans_lt hdiscount)
        hdiscount1
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro _ _ _ a
    exact False.elim (hnonempty ⟨a, Finset.mem_univ a⟩)

/-- One periodic continuation is close to the uniform cycle average for
sufficiently patient players. -/
theorem exists_discountFactor_threshold_periodicContinuation
    (G : UtilityGame ι) {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G.form.sig) (start : ℕ) (who : ι)
    (hcycle : ∀ j, UtilityIntegrable G.utility who
      (G.form.play (cycle j)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ threshold : ℝ, 0 ≤ threshold ∧ threshold < 1 ∧
      ∀ (discount : ℝ) (hdiscount0 : 0 ≤ discount),
        threshold < discount → (hdiscount1 : discount < 1) →
        |G.discountedContinuationPayoff discount
            (fun t => cycle (Fin.ofNat n t)) start who
            (G.periodicContinuationStageIntegrable cycle start who hcycle)
            (G.periodicContinuationSummable
              hdiscount0 hdiscount1 cycle start who hcycle) -
          G.cycleAveragePayoff cycle who hcycle| < ε := by
  obtain ⟨threshold, hthreshold0, hthreshold1, hthreshold⟩ :=
    exists_discountFactor_threshold_weighted_cycleAverage
      (fun j : Fin n =>
        G.stagePayoff (cycle (Fin.ofNat n (start + j))) who
          (hcycle (Fin.ofNat n (start + j)))) hε
  refine ⟨threshold, hthreshold0, hthreshold1, ?_⟩
  intro discount hdiscount0 hdiscount hdiscount1
  have hclose := hthreshold discount hdiscount hdiscount1
  have hrotate :
      (∑ j : Fin n,
          G.stagePayoff (cycle (Fin.ofNat n (start + j))) who
            (hcycle (Fin.ofNat n (start + j)))) =
        ∑ j : Fin n, G.stagePayoff (cycle j) who (hcycle j) :=
    GameTheory.Math.sum_finRotate start fun j : Fin n =>
      G.stagePayoff (cycle j) who (hcycle j)
  rw [hrotate] at hclose
  rw [G.discountedContinuationPayoff_periodicPath_eq
    hdiscount0 hdiscount1 cycle start who hcycle]
  simpa [cycleAveragePayoff] using hclose

/-- One threshold works for every player and every phase of a finite cycle. -/
theorem exists_discountFactor_threshold_periodicAllContinuations
    (G : UtilityGame ι) [Fintype ι]
    {n : ℕ} [NeZero n] (cycle : Fin n → Profile G.form.sig)
    (hcycle : ∀ (who : ι) (j : Fin n),
      UtilityIntegrable G.utility who (G.form.play (cycle j)))
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ threshold : ℝ, 0 ≤ threshold ∧ threshold < 1 ∧
      ∀ (discount : ℝ) (hdiscount0 : 0 ≤ discount),
        threshold < discount → (hdiscount1 : discount < 1) →
        ∀ (who : ι) (start : ℕ),
          |G.discountedContinuationPayoff discount
              (fun t => cycle (Fin.ofNat n t)) start who
              (G.periodicContinuationStageIntegrable cycle start who
                (hcycle who))
              (G.periodicContinuationSummable
                hdiscount0
                hdiscount1 cycle start who (hcycle who)) -
            G.cycleAveragePayoff cycle who (hcycle who)| < ε := by
  let phase := ι × Fin n
  let property : phase → ℝ → Prop := fun a discount =>
    ∀ (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1),
      |G.discountedContinuationPayoff discount
          (fun t => cycle (Fin.ofNat n t)) (a.2 : ℕ) a.1
          (G.periodicContinuationStageIntegrable cycle (a.2 : ℕ)
            a.1 (hcycle a.1))
          (G.periodicContinuationSummable hdiscount0
            hdiscount1 cycle (a.2 : ℕ) a.1 (hcycle a.1)) -
        G.cycleAveragePayoff cycle a.1 (hcycle a.1)| < ε
  have hphase : ∀ a : phase, ∃ threshold : ℝ,
      0 ≤ threshold ∧ threshold < 1 ∧
        ∀ discount : ℝ, threshold < discount → discount < 1 →
          property a discount := by
    intro a
    obtain ⟨candidate, hc0, hc1, hc⟩ :=
      G.exists_discountFactor_threshold_periodicContinuation
        cycle (a.2 : ℕ) a.1 (hcycle a.1) hε
    refine ⟨candidate, hc0, hc1, ?_⟩
    intro discount hcandidate hdiscount1 hdiscount0 _
    exact hc discount hdiscount0 hcandidate hdiscount1
  obtain ⟨threshold, hthreshold0, hthreshold1, hthreshold⟩ :=
    exists_common_discountFactor_threshold (property := property) hphase
  refine ⟨threshold, hthreshold0, hthreshold1, ?_⟩
  intro discount hdiscount0 hdiscount hdiscount1 who start
  have hfinite :=
    hthreshold discount hdiscount hdiscount1
      (who, Fin.ofNat n start) hdiscount0 hdiscount1
  have hstart :
      G.discountedContinuationPayoff discount
          (fun t => cycle (Fin.ofNat n t)) start who
          (G.periodicContinuationStageIntegrable cycle start who (hcycle who))
          (G.periodicContinuationSummable hdiscount0 hdiscount1
            cycle start who (hcycle who)) =
        G.discountedContinuationPayoff discount
          (fun t => cycle (Fin.ofNat n t))
          ((Fin.ofNat n start).val) who
          (G.periodicContinuationStageIntegrable cycle
            ((Fin.ofNat n start).val) who (hcycle who))
          (G.periodicContinuationSummable hdiscount0 hdiscount1
            cycle ((Fin.ofNat n start).val) who (hcycle who)) := by
    simp only [discountedContinuationPayoff,
      GameTheory.Math.normalizedDiscountedSum]
    congr 1
    apply tsum_congr
    intro k
    congr 1
    simp [Fin.ofNat, Nat.add_mod]
  rw [hstart]
  exact hfinite

end UtilityGame

end GameTheory
