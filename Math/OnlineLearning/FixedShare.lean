/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.OnlineLearning.MultiplicativeWeights

/-!
# Fixed-share exponential weights

This file gives the deterministic core of a horizon-free tracking forecaster.
The transition kernel may vary with time.  Consequently the results apply in
particular to decreasing-share kernels.

The algorithm multiplies the current weights by `exp (η * gain)` and then
pushes them through the next share kernel.  Its prediction is the normalized
current weight vector.  Against any comparator path, regret is bounded by
the negative logarithm of that path's Markov prior divided by `η`, plus
`η * T`.

The fixed-rate result is followed by a finite expert master.  Instantiating
its experts with dyadic learning rates gives simultaneous path-regret bounds
for every rate in a predetermined pool.  The pool may be selected from the
current deterministic epoch, while the successful rate is chosen only in
the analysis.
-/

namespace Math.OnlineLearning

variable {A : Type*} [Fintype A] [Nonempty A]

/-- A finite stochastic kernel, represented by its real-valued rows. -/
structure ShareKernel (A : Type*) [Fintype A] where
  prob : A → A → ℝ
  nonneg : ∀ a b, 0 ≤ prob a b
  sum_row : ∀ a, ∑ b, prob a b = 1

/-- The decreasing-share kernel.  At transition `n`, it keeps the current
action with mass `n / (n + 1)` and restarts uniformly with the remaining
mass. -/
noncomputable def decreasingShareKernel (n : ℕ) : ShareKernel A := by
  classical
  refine
    { prob := fun a b =>
        (n : ℝ) / (n + 1) * (if b = a then 1 else 0) +
          1 / ((Fintype.card A : ℝ) * (n + 1))
      nonneg := ?_
      sum_row := ?_ }
  · intro a b
    split <;> positivity
  · intro a
    have hcard : (Fintype.card A : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_pos,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

theorem decreasingShareKernel_switch
    (n : ℕ) {a b : A} (h : b ≠ a) :
    (decreasingShareKernel n).prob a b =
      1 / ((Fintype.card A : ℝ) * (n + 1)) := by
  classical
  change
    (n : ℝ) / (n + 1) * (if b = a then 1 else 0) +
      1 / ((Fintype.card A : ℝ) * (n + 1)) =
        1 / ((Fintype.card A : ℝ) * (n + 1))
  rw [if_neg h, mul_zero, zero_add]

theorem decreasingShareKernel_stay_ge (n : ℕ) (a : A) :
    (n : ℝ) / (n + 1) ≤
      (decreasingShareKernel n).prob a a := by
  classical
  change
    (n : ℝ) / (n + 1) ≤
      (n : ℝ) / (n + 1) * (if a = a then 1 else 0) +
        1 / ((Fintype.card A : ℝ) * (n + 1))
  rw [if_pos rfl, mul_one]
  exact le_add_of_nonneg_right (by positivity)

/-- Number of changes in the first `T` transitions of a comparator path. -/
noncomputable def sharePathSwitchCount (path : ℕ → A) (T : ℕ) : ℕ := by
  classical
  exact ∑ t ∈ Finset.range T, if path (t + 1) ≠ path t then 1 else 0

/-- Uniform distribution used to initialize decreasing fixed share. -/
noncomputable def uniformSharePrior (_a : A) : ℝ :=
  1 / Fintype.card A

omit [Nonempty A] in
theorem uniformSharePrior_nonneg (a : A) : 0 ≤ uniformSharePrior a := by
  unfold uniformSharePrior
  positivity

theorem sum_uniformSharePrior : ∑ a : A, uniformSharePrior a = 1 := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [uniformSharePrior, hcard]

private theorem prod_succ_div_succ_succ (T : ℕ) :
    (∏ t ∈ Finset.range T, ((t : ℝ) + 1) / ((t : ℝ) + 2)) =
      1 / ((T : ℝ) + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.prod_range_succ, ih]
      push_cast
      field_simp
      ring

/-- Markov-prior mass of a comparator path through its first `T`
transitions. -/
noncomputable def sharePathPrior
    (prior : A → ℝ) (Q : ℕ → ShareKernel A)
    (path : ℕ → A) (T : ℕ) : ℝ :=
  prior (path 0) *
    ∏ t ∈ Finset.range T, (Q (t + 1)).prob (path t) (path (t + 1))

/-- The decreasing-share Markov prior charges a path according to its
number of switches. -/
theorem decreasingShare_pathPrior_lower
    (path : ℕ → A) (T : ℕ) :
    (1 / ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) ^
        (sharePathSwitchCount path T + 1) ≤
      sharePathPrior uniformSharePrior decreasingShareKernel path T := by
  classical
  let c : ℝ := 1 / ((Fintype.card A : ℝ) * ((T : ℝ) + 1))
  let stay : ℕ → ℝ := fun t => ((t : ℝ) + 1) / ((t : ℝ) + 2)
  let switched : ℕ → ℕ := fun t => if path (t + 1) ≠ path t then 1 else 0
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hstay_nonneg : ∀ t, 0 ≤ stay t := by
    intro t
    dsimp [stay]
    positivity
  have hfactor :
      ∀ t ∈ Finset.range T,
        c ^ switched t * stay t ≤
          (decreasingShareKernel (t + 1)).prob (path t) (path (t + 1)) := by
    intro t ht
    have htT : t < T := Finset.mem_range.mp ht
    have htcast : (t : ℝ) + 1 ≤ T := by
      exact_mod_cast (Nat.succ_le_iff.mpr htT)
    by_cases hswitch : path (t + 1) ≠ path t
    · rw [decreasingShareKernel_switch (t + 1) hswitch]
      simp only [switched, if_pos hswitch, pow_one]
      dsimp [c, stay]
      have hcard : (0 : ℝ) < Fintype.card A := by
        exact_mod_cast Fintype.card_pos
      have hT : (0 : ℝ) < T + 1 := by positivity
      have ht2 : (0 : ℝ) < t + 2 := by positivity
      calc
        1 / ((Fintype.card A : ℝ) * ((T : ℝ) + 1)) *
              (((t : ℝ) + 1) / ((t : ℝ) + 2)) =
            ((t : ℝ) + 1) /
              (((Fintype.card A : ℝ) * ((T : ℝ) + 1)) *
                ((t : ℝ) + 2)) := by
          field_simp
        _ ≤ ((T : ℝ) + 1) /
              (((Fintype.card A : ℝ) * ((T : ℝ) + 1)) *
                ((t : ℝ) + 2)) := by
          gcongr
        _ = 1 /
              ((Fintype.card A : ℝ) * (((t + 1 : ℕ) : ℝ) + 1)) := by
          push_cast
          field_simp
          ring
    · have hstay := decreasingShareKernel_stay_ge (t + 1) (path t)
      simp only [switched, if_neg hswitch, pow_zero, one_mul]
      rw [not_ne_iff.mp hswitch]
      dsimp [stay]
      convert hstay using 1
      · push_cast
        ring
  have hprod :
      (∏ t ∈ Finset.range T, c ^ switched t * stay t) ≤
        ∏ t ∈ Finset.range T,
          (decreasingShareKernel (t + 1)).prob (path t) (path (t + 1)) :=
    Finset.prod_le_prod
      (fun t ht => mul_nonneg (pow_nonneg hc _) (hstay_nonneg t))
      hfactor
  have hleft :
      (∏ t ∈ Finset.range T, c ^ switched t * stay t) =
        c ^ sharePathSwitchCount path T / ((T : ℝ) + 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [prod_succ_div_succ_succ]
    simp only [sharePathSwitchCount, switched]
    rw [div_eq_mul_inv]
    ring
  rw [sharePathPrior, uniformSharePrior]
  rw [hleft] at hprod
  have hcard : (0 : ℝ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  dsimp [c] at hprod ⊢
  calc
    (1 / ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) ^
          (sharePathSwitchCount path T + 1) =
        (1 / ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) ^
            sharePathSwitchCount path T /
          ((Fintype.card A : ℝ) * ((T : ℝ) + 1)) := by
      rw [pow_succ]
      field_simp
    _ ≤
        (1 / Fintype.card A) *
          ∏ t ∈ Finset.range T,
            (decreasingShareKernel (t + 1)).prob (path t) (path (t + 1)) := by
      calc
        (1 / ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) ^
              sharePathSwitchCount path T /
            ((Fintype.card A : ℝ) * ((T : ℝ) + 1)) =
            (1 / Fintype.card A) *
              ((1 / ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) ^
                sharePathSwitchCount path T / ((T : ℝ) + 1)) := by
          field_simp
        _ ≤
            (1 / Fintype.card A) *
              ∏ t ∈ Finset.range T,
                (decreasingShareKernel (t + 1)).prob
                  (path t) (path (t + 1)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)

/-- Unnormalized fixed-share weights after `t` rounds. -/
noncomputable def fixedShareWeight
    (η : ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) : ℕ → A → ℝ
  | 0, a => prior a
  | t + 1, b =>
      ∑ a, fixedShareWeight η g prior Q t a *
        Real.exp (η * g t a) * (Q (t + 1)).prob a b

/-- Total unnormalized mass at the start of round `t`. -/
noncomputable def fixedShareMass
    (η : ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) (t : ℕ) : ℝ :=
  ∑ a, fixedShareWeight η g prior Q t a

/-- The normalized probability assigned to action `a` at round `t`. -/
noncomputable def fixedShareProb
    (η : ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) (t : ℕ) (a : A) : ℝ :=
  fixedShareWeight η g prior Q t a /
    fixedShareMass η g prior Q t

/-- Gain predicted by normalized fixed-share weights at round `t`. -/
noncomputable def fixedShareRoundGain
    (η : ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) (t : ℕ) : ℝ :=
  (∑ a, fixedShareWeight η g prior Q t a * g t a) /
    fixedShareMass η g prior Q t

/-- Cumulative gain predicted by fixed share through round `T - 1`. -/
noncomputable def fixedShareGain
    (η : ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, fixedShareRoundGain η g prior Q t

/-- Comparator gain through its first `T` actions. -/
def sharePathGain (g : ℕ → A → ℝ) (path : ℕ → A) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, g t (path t)

omit [Nonempty A] in
@[simp] theorem fixedShareWeight_zero
    (η : ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) (a : A) :
    fixedShareWeight η g prior Q 0 a = prior a := rfl

omit [Nonempty A] in
@[simp] theorem fixedShareMass_zero
    (η : ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) :
    fixedShareMass η g prior Q 0 = ∑ a, prior a := by
  simp [fixedShareMass]

omit [Nonempty A] in
@[simp] theorem sharePathPrior_zero
    (prior : A → ℝ) (Q : ℕ → ShareKernel A) (path : ℕ → A) :
    sharePathPrior prior Q path 0 = prior (path 0) := by
  simp [sharePathPrior]

omit [Fintype A] [Nonempty A] in
@[simp] theorem sharePathGain_zero (g : ℕ → A → ℝ) (path : ℕ → A) :
    sharePathGain g path 0 = 0 := by
  simp [sharePathGain]

omit [Fintype A] [Nonempty A] in
theorem sharePathGain_succ (g : ℕ → A → ℝ) (path : ℕ → A) (T : ℕ) :
    sharePathGain g path (T + 1) =
      sharePathGain g path T + g T (path T) := by
  simp [sharePathGain, Finset.sum_range_succ]

omit [Nonempty A] in
theorem sharePathPrior_succ
    (prior : A → ℝ) (Q : ℕ → ShareKernel A)
    (path : ℕ → A) (T : ℕ) :
    sharePathPrior prior Q path (T + 1) =
      sharePathPrior prior Q path T *
        (Q (T + 1)).prob (path T) (path (T + 1)) := by
  simp [sharePathPrior, Finset.prod_range_succ]
  ring

omit [Nonempty A] in
/-- The share step preserves the mass obtained after exponential update. -/
theorem fixedShareMass_succ
    (η : ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) (t : ℕ) :
    fixedShareMass η g prior Q (t + 1) =
      ∑ a, fixedShareWeight η g prior Q t a * Real.exp (η * g t a) := by
  rw [fixedShareMass]
  simp only [fixedShareWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, (Q (t + 1)).sum_row]
  ring

omit [Nonempty A] in
theorem fixedShareWeight_nonneg
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (η : ℝ) (g : ℕ → A → ℝ) (Q : ℕ → ShareKernel A) :
    ∀ t a, 0 ≤ fixedShareWeight η g prior Q t a := by
  intro t
  induction t with
  | zero => exact hprior
  | succ t ih =>
      intro b
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg
          (mul_nonneg (ih a) (Real.exp_pos _).le)
          ((Q (t + 1)).nonneg a b)

omit [Nonempty A] in
theorem fixedShareMass_pos
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (hsum : ∑ a, prior a = 1)
    (η : ℝ) (g : ℕ → A → ℝ) (Q : ℕ → ShareKernel A) :
    ∀ t, 0 < fixedShareMass η g prior Q t := by
  intro t
  induction t with
  | zero => simp [fixedShareMass, hsum]
  | succ t ih =>
      rw [fixedShareMass_succ]
      have hnonneg := fixedShareWeight_nonneg hprior η g Q t
      have hexp : ∀ a, 0 < Real.exp (η * g t a) := fun a => Real.exp_pos _
      have hsome : ∃ a, 0 < fixedShareWeight η g prior Q t a := by
        by_contra h
        push Not at h
        have hz : ∀ a, fixedShareWeight η g prior Q t a = 0 :=
          fun a => le_antisymm (h a) (hnonneg a)
        simp [fixedShareMass, hz] at ih
      obtain ⟨a, ha⟩ := hsome
      exact Finset.sum_pos'
        (fun b _ => mul_nonneg (hnonneg b) (hexp b).le)
        ⟨a, Finset.mem_univ a, mul_pos ha (hexp a)⟩

omit [Nonempty A] in
theorem fixedShareProb_nonneg
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (η : ℝ) (g : ℕ → A → ℝ) (Q : ℕ → ShareKernel A)
    (t : ℕ) (a : A) :
    0 ≤ fixedShareProb η g prior Q t a := by
  exact div_nonneg
    (fixedShareWeight_nonneg hprior η g Q t a)
    (Finset.sum_nonneg fun b _ =>
      fixedShareWeight_nonneg hprior η g Q t b)

omit [Nonempty A] in
theorem sum_fixedShareProb
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (hsum : ∑ a, prior a = 1)
    (η : ℝ) (g : ℕ → A → ℝ) (Q : ℕ → ShareKernel A)
    (t : ℕ) :
    ∑ a, fixedShareProb η g prior Q t a = 1 := by
  have hmass := fixedShareMass_pos hprior hsum η g Q t
  unfold fixedShareProb
  rw [← Finset.sum_div, fixedShareMass]
  exact div_self hmass.ne'

omit [Nonempty A] in
theorem fixedShareRoundGain_eq_sum_prob
    (prior : A → ℝ) (η : ℝ) (g : ℕ → A → ℝ)
    (Q : ℕ → ShareKernel A)
    (t : ℕ) :
    fixedShareRoundGain η g prior Q t =
      ∑ a, fixedShareProb η g prior Q t a * g t a := by
  unfold fixedShareRoundGain fixedShareProb
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]

/-- Second-order exponential bound used by the potential argument. -/
theorem exp_mul_gain_le
    {η x : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.exp (η * x) ≤ 1 + η * x + η ^ 2 := by
  have habsη : |η| ≤ 1 := abs_le.mpr ⟨by linarith, hη1⟩
  have habsx : |x| ≤ 1 := abs_le.mpr hx
  have hy : |η * x| ≤ 1 := by
    rw [abs_mul]
    calc
      |η| * |x| ≤ 1 * 1 := mul_le_mul habsη habsx (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have hb := Real.exp_bound hy (n := 2) (by norm_num)
  have hsum :
      (∑ m ∈ Finset.range 2, (η * x) ^ m / (m.factorial : ℝ)) =
        1 + η * x := by
    norm_num [Finset.sum_range_succ]
  rw [hsum, sq_abs] at hb
  norm_num [Nat.factorial] at hb
  have hsq : (η * x) ^ 2 ≤ η ^ 2 := by
    have hx_sq : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    calc
      (η * x) ^ 2 = η ^ 2 * x ^ 2 := by ring
      _ ≤ η ^ 2 * 1 := mul_le_mul_of_nonneg_left hx_sq (sq_nonneg η)
      _ = η ^ 2 := by ring
  nlinarith [hb, le_abs_self (Real.exp (η * x) - (1 + η * x))]

omit [Nonempty A] in
/-- One-step potential bound for fixed-share exponential weights. -/
theorem fixedShareMass_succ_le
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (hsum : ∑ a, prior a = 1)
    (Q : ℕ → ShareKernel A) (t : ℕ) :
    fixedShareMass η g prior Q (t + 1) ≤
      fixedShareMass η g prior Q t *
        Real.exp (η * fixedShareRoundGain η g prior Q t + η ^ 2) := by
  rw [fixedShareMass_succ]
  have hnonneg := fixedShareWeight_nonneg hprior η g Q t
  have hbound :
      ∑ a, fixedShareWeight η g prior Q t a * Real.exp (η * g t a) ≤
        ∑ a, fixedShareWeight η g prior Q t a *
          (1 + η * g t a + η ^ 2) := by
    exact Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left
        (exp_mul_gain_le hη.le hη1 (hg t a)) (hnonneg a)
  have hmass := fixedShareMass_pos hprior hsum η g Q t
  have hmean :
      fixedShareMass η g prior Q t *
          fixedShareRoundGain η g prior Q t =
        ∑ a, fixedShareWeight η g prior Q t a * g t a := by
    rw [fixedShareRoundGain, mul_div_cancel₀ _ hmass.ne']
  calc
    ∑ a, fixedShareWeight η g prior Q t a * Real.exp (η * g t a)
        ≤ ∑ a, fixedShareWeight η g prior Q t a *
            (1 + η * g t a + η ^ 2) := hbound
    _ = fixedShareMass η g prior Q t *
          (1 + η * fixedShareRoundGain η g prior Q t + η ^ 2) := by
        have hone :
            (∑ a, fixedShareWeight η g prior Q t a * 1) =
              fixedShareMass η g prior Q t := by
          simp [fixedShareMass]
        have hgain :
            (∑ a, fixedShareWeight η g prior Q t a * (η * g t a)) =
              η * (∑ a, fixedShareWeight η g prior Q t a * g t a) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
        have hsquare :
            (∑ a, fixedShareWeight η g prior Q t a * η ^ 2) =
              fixedShareMass η g prior Q t * η ^ 2 := by
          rw [← Finset.sum_mul, fixedShareMass]
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [hone, hgain, hsquare, ← hmean]
        ring
    _ ≤ fixedShareMass η g prior Q t *
          Real.exp (η * fixedShareRoundGain η g prior Q t + η ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hmass.le
        nlinarith [Real.add_one_le_exp
          (η * fixedShareRoundGain η g prior Q t + η ^ 2)]

omit [Nonempty A] in
theorem fixedShareGain_succ
    (η : ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) (T : ℕ) :
    fixedShareGain η g prior Q (T + 1) =
      fixedShareGain η g prior Q T +
        fixedShareRoundGain η g prior Q T := by
  simp [fixedShareGain, Finset.sum_range_succ]

omit [Nonempty A] in
/-- Telescoped potential upper bound. -/
theorem fixedShareMass_le
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (hsum : ∑ a, prior a = 1)
    (Q : ℕ → ShareKernel A) (T : ℕ) :
    fixedShareMass η g prior Q T ≤
      Real.exp (η * fixedShareGain η g prior Q T + η ^ 2 * T) := by
  induction T with
  | zero => simp [fixedShareMass, fixedShareGain, hsum]
  | succ T ih =>
      calc
        fixedShareMass η g prior Q (T + 1) ≤
            fixedShareMass η g prior Q T *
              Real.exp (η * fixedShareRoundGain η g prior Q T + η ^ 2) :=
          fixedShareMass_succ_le hη hη1 hg hprior hsum Q T
        _ ≤ Real.exp (η * fixedShareGain η g prior Q T + η ^ 2 * T) *
              Real.exp (η * fixedShareRoundGain η g prior Q T + η ^ 2) :=
          mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = Real.exp
              (η * fixedShareGain η g prior Q (T + 1) +
                η ^ 2 * ((T + 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_add, fixedShareGain_succ]
          push_cast
          congr 1
          ring

omit [Nonempty A] in
/-- The mass along one comparator path survives every update and share
step. -/
theorem sharePathPrior_mul_exp_gain_le_weight
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (η : ℝ) (g : ℕ → A → ℝ) (Q : ℕ → ShareKernel A)
    (path : ℕ → A) (T : ℕ) :
    sharePathPrior prior Q path T *
        Real.exp (η * sharePathGain g path T) ≤
      fixedShareWeight η g prior Q T (path T) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [sharePathPrior_succ, sharePathGain_succ, mul_add, Real.exp_add]
      rw [fixedShareWeight]
      have hq := (Q (T + 1)).nonneg (path T) (path (T + 1))
      have hexp := (Real.exp_pos (η * g T (path T))).le
      calc
        (sharePathPrior prior Q path T *
              (Q (T + 1)).prob (path T) (path (T + 1))) *
            (Real.exp (η * sharePathGain g path T) *
              Real.exp (η * g T (path T))) =
            (sharePathPrior prior Q path T *
              Real.exp (η * sharePathGain g path T)) *
              Real.exp (η * g T (path T)) *
              (Q (T + 1)).prob (path T) (path (T + 1)) := by ring
        _ ≤ fixedShareWeight η g prior Q T (path T) *
              Real.exp (η * g T (path T)) *
              (Q (T + 1)).prob (path T) (path (T + 1)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ih hexp) hq
        _ ≤ ∑ a, fixedShareWeight η g prior Q T a *
              Real.exp (η * g T a) *
              (Q (T + 1)).prob a (path (T + 1)) :=
          Finset.single_le_sum
            (fun a _ =>
              mul_nonneg
                (mul_nonneg
                  (fixedShareWeight_nonneg hprior η g Q T a)
                  (Real.exp_pos (η * g T a)).le)
                ((Q (T + 1)).nonneg a (path (T + 1))))
            (Finset.mem_univ (path T))

omit [Nonempty A] in
/-- Fixed-rate tracking regret against an arbitrary comparator path.

`code` is any upper bound on the negative log Markov prior, expressed
without logarithms as `exp (-code) ≤ pathPrior`. -/
theorem fixedShare_path_regret_le
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (hsum : ∑ a, prior a = 1)
    (Q : ℕ → ShareKernel A) (path : ℕ → A) (T : ℕ)
    {code : ℝ} (hcode : Real.exp (-code) ≤ sharePathPrior prior Q path T) :
    sharePathGain g path T - fixedShareGain η g prior Q T ≤
      code / η + η * T := by
  have hpath :=
    sharePathPrior_mul_exp_gain_le_weight hprior η g Q path T
  have hweight :
      fixedShareWeight η g prior Q T (path T) ≤
        fixedShareMass η g prior Q T := by
    exact Finset.single_le_sum
      (fun a _ => fixedShareWeight_nonneg hprior η g Q T a)
      (Finset.mem_univ (path T))
  have hmass :=
    fixedShareMass_le hη hη1 hg hprior hsum Q T
  have hchain :
      Real.exp (-code + η * sharePathGain g path T) ≤
        Real.exp (η * fixedShareGain η g prior Q T + η ^ 2 * T) := by
    rw [Real.exp_add]
    exact (mul_le_mul_of_nonneg_right hcode (Real.exp_pos _).le).trans <|
      hpath.trans <| hweight.trans hmass
  rw [Real.exp_le_exp] at hchain
  have hηne : η ≠ 0 := hη.ne'
  have hrewrite :
      code / η + η * T = (code + η ^ 2 * T) / η := by
    field_simp
  rw [hrewrite, le_div_iff₀ hη]
  nlinarith

/-- Explicit coding cost of a path under decreasing fixed share. -/
noncomputable def decreasingShareCode (path : ℕ → A) (T : ℕ) : ℝ :=
  (sharePathSwitchCount path T + 1) *
    Real.log ((Fintype.card A : ℝ) * ((T : ℝ) + 1))

/-- Horizon-free, fixed-learning-rate switching-regret bound for decreasing
fixed share.  The algorithm is defined for all times before `T` and `path`
are supplied to the theorem. -/
theorem decreasingFixedShare_path_regret_le
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (path : ℕ → A) (T : ℕ) :
    sharePathGain g path T -
        fixedShareGain η g uniformSharePrior decreasingShareKernel T ≤
      decreasingShareCode path T / η + η * T := by
  have hbase :
      0 < (Fintype.card A : ℝ) * ((T : ℝ) + 1) := by
    have hcard : (0 : ℝ) < Fintype.card A := by
      exact_mod_cast Fintype.card_pos
    exact mul_pos hcard (by positivity)
  have hexp :
      Real.exp (-decreasingShareCode path T) =
        (1 / ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) ^
          (sharePathSwitchCount path T + 1) := by
    rw [decreasingShareCode]
    have heq :
        -(((sharePathSwitchCount path T : ℝ) + 1) *
            Real.log ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) =
          ((sharePathSwitchCount path T + 1 : ℕ) : ℝ) *
            (-Real.log ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) := by
      push_cast
      ring
    rw [heq, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hbase]
    congr 1
    field_simp
  apply fixedShare_path_regret_le hη hη1 hg uniformSharePrior_nonneg
    sum_uniformSharePrior decreasingShareKernel path T
  rw [hexp]
  exact decreasingShare_pathPrior_lower path T

omit [Nonempty A] in
/-- A fixed-share round gain is a convex combination of the action gains. -/
theorem fixedShareRoundGain_mem_Icc
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (hsum : ∑ a, prior a = 1)
    (η : ℝ) {g : ℕ → A → ℝ}
    (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (Q : ℕ → ShareKernel A) (t : ℕ) :
    fixedShareRoundGain η g prior Q t ∈ Set.Icc (-1 : ℝ) 1 := by
  have hprob_nonneg :
      ∀ a, 0 ≤ fixedShareProb η g prior Q t a :=
    fixedShareProb_nonneg hprior η g Q t
  have hprob_sum :
      ∑ a, fixedShareProb η g prior Q t a = 1 :=
    sum_fixedShareProb hprior hsum η g Q t
  rw [fixedShareRoundGain_eq_sum_prob]
  constructor
  · calc
      (-1 : ℝ) = ∑ a, fixedShareProb η g prior Q t a * (-1 : ℝ) := by
        rw [← Finset.sum_mul, hprob_sum]
        ring
      _ ≤ ∑ a, fixedShareProb η g prior Q t a * g t a :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hg t a).1 (hprob_nonneg a)
  · calc
      ∑ a, fixedShareProb η g prior Q t a * g t a ≤
          ∑ a, fixedShareProb η g prior Q t a * (1 : ℝ) :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hg t a).2 (hprob_nonneg a)
      _ = 1 := by
        rw [← Finset.sum_mul, hprob_sum]
        ring

section FiniteRateMaster

variable {J : Type*} [Fintype J] [Nonempty J]

/-- Gain stream presented to the master: expert `j` is the fixed-share
forecaster with learning rate `rate j`. -/
noncomputable def fixedShareExpertRoundGain
    (rate : J → ℝ) (g : ℕ → A → ℝ) (prior : A → ℝ)
    (Q : ℕ → ShareKernel A) (t : ℕ) (j : J) : ℝ :=
  fixedShareRoundGain (rate j) g prior Q t

/-- A finite exponential-weights master over fixed-share learning rates. -/
noncomputable def fixedShareMasterGain
    (masterRate : ℝ) (rate : J → ℝ) (g : ℕ → A → ℝ)
    (prior : A → ℝ) (Q : ℕ → ShareKernel A) (T : ℕ) : ℝ :=
  signedAlgGain masterRate
    (fixedShareExpertRoundGain rate g prior Q) T

omit [Nonempty A] [Fintype J] [Nonempty J] in
theorem fixedShareExpertRoundGain_mem_Icc
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (hsum : ∑ a, prior a = 1)
    (rate : J → ℝ) {g : ℕ → A → ℝ}
    (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (Q : ℕ → ShareKernel A) :
    ∀ t j,
      fixedShareExpertRoundGain rate g prior Q t j ∈
        Set.Icc (-1 : ℝ) 1 :=
  fun t j =>
    fixedShareRoundGain_mem_Icc hprior hsum (rate j) hg Q t

omit [Nonempty A] in
/-- Deterministic finite-rate master bound.  The comparator may choose the
best learning rate after the gain sequence and path are known. -/
theorem fixedShareMaster_path_regret_le
    {masterRate : ℝ} (hmaster : 0 < masterRate)
    (hmaster_one : masterRate ≤ 1)
    {rate : J → ℝ} (hrate_pos : ∀ j, 0 < rate j)
    (hrate_one : ∀ j, rate j ≤ 1)
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    {prior : A → ℝ} (hprior : ∀ a, 0 ≤ prior a)
    (hsum : ∑ a, prior a = 1)
    (Q : ℕ → ShareKernel A) (path : ℕ → A) (T : ℕ)
    {code : ℝ} (hcode : Real.exp (-code) ≤ sharePathPrior prior Q path T)
    (j : J) :
    sharePathGain g path T -
        fixedShareMasterGain masterRate rate g prior Q T ≤
      code / rate j + rate j * T +
        2 * (Real.log (Fintype.card J) / masterRate +
          masterRate * T) := by
  have hfixed :=
    fixedShare_path_regret_le (hrate_pos j) (hrate_one j)
      hg hprior hsum Q path T hcode
  have hexpert :=
    fixedShareExpertRoundGain_mem_Icc hprior hsum rate hg Q
  have hmaster_regret :=
    signed_fixedActionRegret_le_of_le_one
      hmaster hmaster_one hexpert T j
  have hcum :
      cumGain (fixedShareExpertRoundGain rate g prior Q) T j =
        fixedShareGain (rate j) g prior Q T := by
    rfl
  rw [hcum] at hmaster_regret
  change
    fixedShareGain (rate j) g prior Q T -
        fixedShareMasterGain masterRate rate g prior Q T ≤
      2 * (Real.log (Fintype.card J) / masterRate +
        masterRate * T) at hmaster_regret
  linarith

/-- Finite-rate master specialized to decreasing share.  Its coding cost is
explicitly `(K + 1) log (m (T + 1))`. -/
theorem decreasingFixedShareMaster_path_regret_le
    {masterRate : ℝ} (hmaster : 0 < masterRate)
    (hmaster_one : masterRate ≤ 1)
    {rate : J → ℝ} (hrate_pos : ∀ j, 0 < rate j)
    (hrate_one : ∀ j, rate j ≤ 1)
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (path : ℕ → A) (T : ℕ) (j : J) :
    sharePathGain g path T -
        fixedShareMasterGain masterRate rate g
          uniformSharePrior decreasingShareKernel T ≤
      decreasingShareCode path T / rate j + rate j * T +
        2 * (Real.log (Fintype.card J) / masterRate +
          masterRate * T) := by
  have hbase :
      0 < (Fintype.card A : ℝ) * ((T : ℝ) + 1) := by
    have hcard : (0 : ℝ) < Fintype.card A := by
      exact_mod_cast Fintype.card_pos
    exact mul_pos hcard (by positivity)
  have hexp :
      Real.exp (-decreasingShareCode path T) =
        (1 / ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) ^
          (sharePathSwitchCount path T + 1) := by
    rw [decreasingShareCode]
    have heq :
        -(((sharePathSwitchCount path T : ℝ) + 1) *
            Real.log ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) =
          ((sharePathSwitchCount path T + 1 : ℕ) : ℝ) *
            (-Real.log ((Fintype.card A : ℝ) * ((T : ℝ) + 1))) := by
      push_cast
      ring
    rw [heq, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hbase]
    congr 1
    field_simp
  apply fixedShareMaster_path_regret_le hmaster hmaster_one
    hrate_pos hrate_one hg uniformSharePrior_nonneg
    sum_uniformSharePrior decreasingShareKernel path T
    (j := j)
  rw [hexp]
  exact decreasingShare_pathPrior_lower path T

end FiniteRateMaster

/-- Dyadic fixed-share learning rates, all chosen independently of gains and
the terminal comparison time. -/
noncomputable def dyadicShareRate (j : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (j + 2)

theorem dyadicShareRate_pos (j : ℕ) : 0 < dyadicShareRate j := by
  unfold dyadicShareRate
  positivity

theorem dyadicShareRate_le_one (j : ℕ) : dyadicShareRate j ≤ 1 := by
  unfold dyadicShareRate
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 2) := by
    exact one_le_pow₀ (by norm_num)
  exact (div_le_one (by positivity)).mpr hpow

/-- The finite dyadic-rate master used in deterministic epoch `pool`.
Increasing `pool` between predetermined epochs yields a single
horizon-independent calendar algorithm. -/
noncomputable def decreasingDyadicFixedShareMasterGain
    (masterRate : ℝ) (pool : ℕ) (g : ℕ → A → ℝ) (T : ℕ) : ℝ :=
  fixedShareMasterGain masterRate
    (fun j : Fin (pool + 1) => dyadicShareRate j)
    g uniformSharePrior decreasingShareKernel T

/-- Post-hoc dyadic-rate switching regret.  Every rate in the predetermined
pool is available simultaneously, and the index `j` is selected only in the
analysis. -/
theorem decreasingDyadicFixedShareMaster_path_regret_le
    {masterRate : ℝ} (hmaster : 0 < masterRate)
    (hmaster_one : masterRate ≤ 1)
    (pool : ℕ)
    {g : ℕ → A → ℝ} (hg : ∀ t a, g t a ∈ Set.Icc (-1 : ℝ) 1)
    (path : ℕ → A) (T : ℕ) (j : Fin (pool + 1)) :
    sharePathGain g path T -
        decreasingDyadicFixedShareMasterGain masterRate pool g T ≤
      decreasingShareCode path T / dyadicShareRate j +
        dyadicShareRate j * T +
        2 * (Real.log (pool + 1) / masterRate +
          masterRate * T) := by
  simpa [decreasingDyadicFixedShareMasterGain] using
    (decreasingFixedShareMaster_path_regret_le
      (J := Fin (pool + 1)) hmaster hmaster_one
      (fun j => dyadicShareRate_pos j)
      (fun j => dyadicShareRate_le_one j)
      hg path T j)

end Math.OnlineLearning
