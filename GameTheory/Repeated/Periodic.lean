/-
# Periodic repeated paths

Exact normalized discounted values of finite cycles and their uniform
convergence to cycle averages as the discount factor tends to one. The proof
inventory is adapted from the pinned v1 `FolkTheorem/Periodic.lean`, but the
result now uses explicit payoff bounds and the canonical list-history path.
-/

import Mathlib.Analysis.SumOverResidueClass
import GameTheory.Repeated.Discounted

noncomputable section

open scoped BigOperators

namespace GameTheory

universe uι

variable {ι : Type uι}

namespace UtilityGame

/-- Sufficient patience makes a fixed continuation margin dominate any bounded
one-period gain. -/
theorem exists_discountFactor_threshold_oneStep
    {gain margin : ℝ} (hgain : 0 ≤ gain) (hmargin : 0 < margin) :
    ∃ threshold : ℝ, 0 ≤ threshold ∧ threshold < 1 ∧
      ∀ discount : ℝ, threshold < discount → discount < 1 →
        (1 - discount) * gain < discount * margin := by
  let threshold : ℝ := gain / (gain + margin)
  have hdenominator : 0 < gain + margin := by linarith
  refine ⟨threshold, div_nonneg hgain hdenominator.le, ?_, ?_⟩
  · rw [div_lt_one hdenominator]
    linarith
  · intro discount hdiscount _
    have hmul : gain < discount * (gain + margin) :=
      (div_lt_iff₀ hdenominator).1 hdiscount
    nlinarith

/-- Average stage payoff of a nonempty finite cycle. -/
def cycleAveragePayoff (G : UtilityGame ι) {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G.form.sig) (who : ι) : ℝ :=
  (n : ℝ)⁻¹ * ∑ t : Fin n, G.stagePayoff (cycle t) who

/-- Equivalence between residues modulo a positive natural and `Fin n`. -/
def zmodFinEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun j := ⟨j.val, j.val_lt⟩
  invFun k := (k.val : ZMod n)
  left_inv j := by
    apply ZMod.val_injective n
    simp
  right_inv k := by
    ext
    simp [Nat.mod_eq_of_lt k.isLt]

theorem finRotate_injective (n : ℕ) [NeZero n] (start : ℕ) :
    Function.Injective (fun j : Fin n => Fin.ofNat n (start + j)) := by
  intro j k h
  apply Fin.ext
  have hval : (start + (j : ℕ)) % n = (start + (k : ℕ)) % n := by
    simpa [Fin.ofNat] using congrArg Fin.val h
  have hz : ((j : ℕ) : ZMod n) = ((k : ℕ) : ZMod n) := by
    have hsum : ((start + (j : ℕ) : ℕ) : ZMod n) =
        ((start + (k : ℕ) : ℕ) : ZMod n) := by
      rw [ZMod.natCast_eq_natCast_iff']
      exact hval
    have hsum' :
        ((start : ZMod n) + ((j : ℕ) : ZMod n)) =
          ((start : ZMod n) + ((k : ℕ) : ZMod n)) := by
      simpa using hsum
    exact add_left_cancel hsum'
  have hmod : (j : ℕ) % n = (k : ℕ) % n := by
    rw [← ZMod.natCast_eq_natCast_iff']
    exact hz
  simpa [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt] using hmod

/-- Rotation by `start` permutes the phases of a nonempty cycle. -/
def finRotateEquiv (n : ℕ) [NeZero n] (start : ℕ) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun j : Fin n => Fin.ofNat n (start + j))
    ⟨finRotate_injective n start,
      Finite.injective_iff_surjective.mp (finRotate_injective n start)⟩

@[simp]
theorem finRotateEquiv_apply (n : ℕ) [NeZero n] (start : ℕ) (j : Fin n) :
    finRotateEquiv n start j = Fin.ofNat n (start + j) :=
  rfl

/-- Rotation does not change a finite cycle sum. -/
theorem sum_finRotate {n : ℕ} [NeZero n] (start : ℕ) (f : Fin n → ℝ) :
    (∑ j : Fin n, f (Fin.ofNat n (start + j))) = ∑ j : Fin n, f j := by
  exact Fintype.sum_equiv (finRotateEquiv n start)
    (fun j : Fin n => f (Fin.ofNat n (start + j))) f
    (fun j => by simp)

/-- Exact normalized discounted payoff of a periodic repeated profile. -/
theorem discountedPayoff_periodicRepeatedProfile_eq
    (G : UtilityGame ι) {n : ℕ} [NeZero n]
    {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (cycle : Fin n → Profile G.form.sig) (who : ι)
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound) :
    G.discountedPayoff discount (G.periodicRepeatedProfile cycle) who =
      (∑ j : Fin n,
          discount ^ (j : ℕ) * G.stagePayoff (cycle j) who) /
        (∑ j : Fin n, discount ^ (j : ℕ)) := by
  let profile : G.RepeatedProfile := G.periodicRepeatedProfile cycle
  have hs : Summable fun t : ℕ =>
      discount ^ t * G.stagePayoff (G.repeatedPlay profile t) who :=
    G.summable_discounted_stagePayoff_of_abs_bound
      hdiscount0 hdiscount1 who hbound
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
  have hsplit :
      (∑' t : ℕ,
          discount ^ t * G.stagePayoff (G.repeatedPlay profile t) who) =
        ∑ j : ZMod n, ∑' m : ℕ,
          discount ^ (j.val + n * m) *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who := by
    rw [Nat.sumByResidueClasses hs n]
    refine Finset.sum_congr rfl ?_
    intro j _
    apply tsum_congr
    intro m
    dsimp [profile]
    rw [G.repeatedPlay_periodicRepeatedProfile]
    congr 2
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt j.val_lt]
  have hinner : ∀ j : ZMod n,
      (∑' m : ℕ,
          discount ^ (j.val + n * m) *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who) =
        (discount ^ j.val *
          G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who) *
            (1 - discount ^ n)⁻¹ := by
    intro j
    calc
      (∑' m : ℕ,
          discount ^ (j.val + n * m) *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who) =
        ∑' m : ℕ,
          (discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who) *
              (discount ^ n) ^ m := by
        apply tsum_congr
        intro m
        rw [pow_add, pow_mul]
        ring
      _ = (discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who) *
          (∑' m : ℕ, (discount ^ n) ^ m) := by
        rw [tsum_mul_left]
      _ = (discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who) *
          (1 - discount ^ n)⁻¹ := by
        rw [tsum_geometric_of_lt_one (pow_nonneg hdiscount0 n) hpow]
  have hzsum :
      (∑ j : ZMod n,
          discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who) =
        ∑ j : Fin n,
          discount ^ (j : ℕ) * G.stagePayoff (cycle j) who := by
    exact Fintype.sum_equiv (zmodFinEquiv n)
      (fun j : ZMod n =>
        discount ^ j.val *
          G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who)
      (fun j : Fin n =>
        discount ^ (j : ℕ) * G.stagePayoff (cycle j) who)
      (fun _ => rfl)
  calc
    G.discountedPayoff discount (G.periodicRepeatedProfile cycle) who =
        (1 - discount) * (∑ j : ZMod n,
          (discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who) *
              (1 - discount ^ n)⁻¹) := by
      simp only [discountedPayoff]
      rw [show G.periodicRepeatedProfile cycle = profile from rfl, hsplit]
      congr 1
      exact Finset.sum_congr rfl fun j _ => hinner j
    _ = (1 - discount) *
        ((∑ j : ZMod n,
          discount ^ j.val *
            G.stagePayoff (cycle ⟨j.val, j.val_lt⟩) who) *
              (1 - discount ^ n)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (∑ j : Fin n,
          discount ^ (j : ℕ) * G.stagePayoff (cycle j) who) /
        (∑ j : Fin n, discount ^ (j : ℕ)) := by
      rw [hzsum, ← hgeom]
      field_simp [hden, hone]

/-- A continuation of a periodic path is the discounted payoff of its rotated
cycle. -/
theorem discountedContinuationPayoff_periodicPath_eq
    (G : UtilityGame ι) {n : ℕ} [NeZero n]
    {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (cycle : Fin n → Profile G.form.sig) (start : ℕ) (who : ι)
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound) :
    G.discountedContinuationPayoff discount
        (fun t => cycle (Fin.ofNat n t)) start who =
      (∑ j : Fin n, discount ^ (j : ℕ) *
          G.stagePayoff (cycle (Fin.ofNat n (start + j))) who) /
        (∑ j : Fin n, discount ^ (j : ℕ)) := by
  let rotated : Fin n → Profile G.form.sig :=
    fun j => cycle (Fin.ofNat n (start + j))
  have hcontinuation :
      G.discountedContinuationPayoff discount
          (fun t => cycle (Fin.ofNat n t)) start who =
        G.discountedPayoff discount
          (G.periodicRepeatedProfile rotated) who := by
    simp only [discountedContinuationPayoff, discountedPayoff]
    congr 1
    apply tsum_congr
    intro k
    congr 2
    unfold rotated
    ext
    simp [Fin.ofNat, Nat.add_mod]
  rw [hcontinuation]
  exact G.discountedPayoff_periodicRepeatedProfile_eq
    hdiscount0 hdiscount1 rotated who hbound

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
    {bound ε : ℝ}
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound)
    (hε : 0 < ε) :
    ∃ threshold : ℝ, 0 ≤ threshold ∧ threshold < 1 ∧
      ∀ discount : ℝ, threshold < discount → discount < 1 →
        |G.discountedContinuationPayoff discount
            (fun t => cycle (Fin.ofNat n t)) start who -
          G.cycleAveragePayoff cycle who| < ε := by
  obtain ⟨threshold, hthreshold0, hthreshold1, hthreshold⟩ :=
    exists_discountFactor_threshold_weighted_cycleAverage
      (fun j : Fin n =>
        G.stagePayoff (cycle (Fin.ofNat n (start + j))) who) hε
  refine ⟨threshold, hthreshold0, hthreshold1, ?_⟩
  intro discount hdiscount hdiscount1
  have hdiscount0 : 0 ≤ discount :=
    le_of_lt (hthreshold0.trans_lt hdiscount)
  have hclose := hthreshold discount hdiscount hdiscount1
  have hrotate :
      (∑ j : Fin n,
          G.stagePayoff (cycle (Fin.ofNat n (start + j))) who) =
        ∑ j : Fin n, G.stagePayoff (cycle j) who :=
    sum_finRotate start fun j : Fin n => G.stagePayoff (cycle j) who
  rw [hrotate] at hclose
  rw [G.discountedContinuationPayoff_periodicPath_eq
    hdiscount0 hdiscount1 cycle start who hbound]
  simpa [cycleAveragePayoff] using hclose

/-- One threshold works for every player and every phase of a finite cycle. -/
theorem exists_discountFactor_threshold_periodicAllContinuations
    (G : UtilityGame ι) [Fintype ι]
    {n : ℕ} [NeZero n] (cycle : Fin n → Profile G.form.sig)
    {bound ε : ℝ}
    (hbound : ∀ (who : ι) (stage : Profile G.form.sig),
      |G.stagePayoff stage who| ≤ bound)
    (hε : 0 < ε) :
    ∃ threshold : ℝ, 0 ≤ threshold ∧ threshold < 1 ∧
      ∀ discount : ℝ, threshold < discount → discount < 1 →
        ∀ (who : ι) (start : ℕ),
          |G.discountedContinuationPayoff discount
              (fun t => cycle (Fin.ofNat n t)) start who -
            G.cycleAveragePayoff cycle who| < ε := by
  let phase := ι × Fin n
  have hphase : ∀ a : phase, ∃ threshold : ℝ,
      0 ≤ threshold ∧ threshold < 1 ∧
        ∀ discount : ℝ, threshold < discount → discount < 1 →
          |G.discountedContinuationPayoff discount
              (fun t => cycle (Fin.ofNat n t)) (a.2 : ℕ) a.1 -
            G.cycleAveragePayoff cycle a.1| < ε := by
    intro a
    exact G.exists_discountFactor_threshold_periodicContinuation
      cycle (a.2 : ℕ) a.1 (hbound a.1) hε
  obtain ⟨threshold, hthreshold0, hthreshold1, hthreshold⟩ :=
    exists_common_discountFactor_threshold hphase
  refine ⟨threshold, hthreshold0, hthreshold1, ?_⟩
  intro discount hdiscount hdiscount1 who start
  have hfinite :=
    hthreshold discount hdiscount hdiscount1
      (who, Fin.ofNat n start)
  have hstart :
      G.discountedContinuationPayoff discount
          (fun t => cycle (Fin.ofNat n t)) start who =
        G.discountedContinuationPayoff discount
          (fun t => cycle (Fin.ofNat n t))
          ((Fin.ofNat n start).val) who := by
    simp only [discountedContinuationPayoff]
    congr 1
    apply tsum_congr
    intro k
    congr 2
    ext
    simp [Fin.ofNat, Nat.add_mod]
  rw [hstart]
  exact hfinite

end UtilityGame

end GameTheory
