/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.InfinitePathSupersolution
import UniformEquilibrium.Quitting.EssentialAPS.OpponentContraction
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Fixed subdivision of nonperiodic singleton-flow paths

A compact terminal-free APS path has a uniform coarse-hazard ceiling below one.
This file develops the deterministic consumer of such a ceiling.  Every coarse
singleton arc is split into the same positive number `m` of logarithmic
microstages.  The construction has three exact features:

* the values close at every coarse boundary;
* prescribed policy evaluation and prescribed Continue remain exact at every
  microstage; and
* the product of the `m` microstage Continue probabilities is the original
  coarse Continue probability.

The immediate-Quit excess is at most `D` times the micro-hazard.  A uniform
coarse-hazard ceiling chooses one finite `m` making this excess arbitrarily
small along the whole nonperiodic path.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math Math.Probability Math.PMFProduct

variable {ι : Type}

/-! ## A uniform mesh scale below a fixed coarse-hazard ceiling -/

/-- Logarithmic intensity is monotone in the stopping hazard on `[0,1)`. -/
theorem quittingMeshIntensity_mono
    {p pStar : ℝ} (_hp0 : 0 ≤ p) (hpLe : p ≤ pStar)
    (hpStar1 : pStar < 1) :
    quittingMeshIntensity p ≤ quittingMeshIntensity pStar := by
  have hp1 : p < 1 := lt_of_le_of_lt hpLe hpStar1
  have hbaseStar : 0 < 1 - pStar := sub_pos.mpr hpStar1
  have hbase : 0 < 1 - p := sub_pos.mpr hp1
  have horder : 1 - pStar ≤ 1 - p := by linarith
  have hlog : Real.log (1 - pStar) ≤ Real.log (1 - p) :=
    Real.strictMonoOn_log.monotoneOn hbaseStar hbase horder
  unfold quittingMeshIntensity
  linarith

/-- One positive integer subdivision count makes every micro-hazard below the
requested error after multiplication by a common collision-surplus bound. -/
theorem exists_uniform_quittingMeshScale
    {pStar D error : ℝ}
    (hpStar0 : 0 ≤ pStar) (hpStar1 : pStar < 1)
    (hD : 0 ≤ D) (herror : 0 < error) :
    ∃ m : ℕ, 0 < m ∧
      ∀ p, 0 ≤ p → p ≤ pStar →
        D * quittingMeshHazard p m ≤ error := by
  let aStar := quittingMeshIntensity pStar
  have haStar0 : 0 ≤ aStar :=
    quittingMeshIntensity_nonneg hpStar0 hpStar1.le
  let ratio := D * aStar / error
  have hratio0 : 0 ≤ ratio := by
    dsimp only [ratio]
    exact div_nonneg (mul_nonneg hD haStar0) herror.le
  obtain ⟨m, hmGt⟩ := exists_nat_gt ratio
  have hmReal : 0 < (m : ℝ) := hratio0.trans_lt hmGt
  have hm : 0 < m := by exact_mod_cast hmReal
  refine ⟨m, hm, ?_⟩
  intro p hp0 hpLe
  have hp1 : p < 1 := lt_of_le_of_lt hpLe hpStar1
  have hintensity : quittingMeshIntensity p ≤ aStar := by
    exact quittingMeshIntensity_mono hp0 hpLe hpStar1
  have hhazard : quittingMeshHazard p m ≤ aStar / (m : ℝ) := by
    exact (quittingMeshHazard_le_intensity_div hp1).trans
      (div_le_div_of_nonneg_right hintensity hmReal.le)
  have hscaledHazard :
      D * quittingMeshHazard p m ≤ D * (aStar / (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hhazard hD
  have hratioEq : D * aStar = ratio * error := by
    dsimp only [ratio]
    field_simp [ne_of_gt herror]
  have hproductLt : D * aStar < error * (m : ℝ) := by
    calc
      D * aStar = ratio * error := hratioEq
      _ < (m : ℝ) * error := mul_lt_mul_of_pos_right hmGt herror
      _ = error * (m : ℝ) := by ring
  have hdivLt : D * aStar / (m : ℝ) < error :=
    (div_lt_iff₀ hmReal).2 (by simpa [mul_comm] using hproductLt)
  calc
    D * quittingMeshHazard p m ≤ D * (aStar / (m : ℝ)) :=
      hscaledHazard
    _ = D * aStar / (m : ℝ) := by ring
    _ ≤ error := hdivLt.le

/-! ## Uniform time dilation -/

/-- Coarse stage containing a microstage of a fixed-width subdivision. -/
def quittingUniformMeshCoarseTime (m time : ℕ) : ℕ := time / m

/-- Offset within the coarse stage of a fixed-width subdivision. -/
def quittingUniformMeshOffset (m time : ℕ) : ℕ := time % m

/-- The active owner is constant throughout each microblock. -/
def quittingUniformMeshOwner
    (owner : ℕ → ι) (m : ℕ) : ℕ → ι :=
  fun time ↦ owner (quittingUniformMeshCoarseTime m time)

/-- Microstage hazard obtained by logarithmically subdividing the containing
coarse hazard. -/
def quittingUniformMeshMass
    (mass : ℕ → ℝ) (m : ℕ) : ℕ → ℝ :=
  fun time ↦ quittingMeshHazard
    (mass (quittingUniformMeshCoarseTime m time)) m

/-- Interpolated payoff at a microstage of a uniformly subdivided path. -/
def quittingUniformMeshValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (m : ℕ) : ℕ → Payoff ι :=
  fun time ↦
    let coarse := quittingUniformMeshCoarseTime m time
    quittingMeshPayoffInterpolant
      (quittingSoloReward reward (owner coarse))
      (value coarse)
      (1 - quittingMeshHazard (mass coarse) m)
      (quittingUniformMeshOffset m time)

@[simp] theorem quittingMeshPayoffInterpolant_zero
    (root start : Payoff ι) (a : ℝ) :
    quittingMeshPayoffInterpolant root start a 0 = start := by
  funext who
  simp [quittingMeshPayoffInterpolant, quittingMeshInterpolant]

/-- Division identifies the coarse block of a block-offset index. -/
theorem quittingUniformMeshCoarseTime_block_add
    {m block offset : ℕ} (hm : 0 < m) (hoffset : offset < m) :
    quittingUniformMeshCoarseTime m (block * m + offset) = block := by
  unfold quittingUniformMeshCoarseTime
  calc
    (block * m + offset) / m = (offset + m * block) / m := by
      congr 1
      ac_rfl
    _ = offset / m + block := Nat.add_mul_div_left offset block hm
    _ = block := by rw [Nat.div_eq_of_lt hoffset, zero_add]

/-- Remainder identifies the offset of a block-offset index. -/
theorem quittingUniformMeshOffset_block_add
    {m block offset : ℕ} (_hm : 0 < m) (hoffset : offset < m) :
    quittingUniformMeshOffset m (block * m + offset) = offset := by
  unfold quittingUniformMeshOffset
  calc
    (block * m + offset) % m = (m * block + offset) % m := by
      congr 1
      ac_rfl
    _ = offset % m := Nat.mul_add_mod_self_left _ _ _
    _ = offset := Nat.mod_eq_of_lt hoffset

/-- Every micro-offset lies below a positive subdivision width. -/
theorem quittingUniformMeshOffset_lt
    {m time : ℕ} (hm : 0 < m) :
    quittingUniformMeshOffset m time < m := by
  unfold quittingUniformMeshOffset
  exact Nat.mod_lt _ hm

/-- The interpolated micro-value at a coarse boundary is the coarse value. -/
@[simp] theorem quittingUniformMeshValue_block
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {m : ℕ} (hm : 0 < m) (block : ℕ) :
    quittingUniformMeshValue reward owner mass value m (block * m) =
      value block := by
  unfold quittingUniformMeshValue
  dsimp only
  have hcoarse : quittingUniformMeshCoarseTime m (block * m) = block := by
    simpa using quittingUniformMeshCoarseTime_block_add
      (block := block) (offset := 0) hm (Nat.zero_lt_of_lt hm)
  have hoffset : quittingUniformMeshOffset m (block * m) = 0 := by
    simpa using quittingUniformMeshOffset_block_add
      (block := block) (offset := 0) hm (Nat.zero_lt_of_lt hm)
  rw [hcoarse, hoffset]
  exact quittingMeshPayoffInterpolant_zero _ _ _

/-- The successor micro-value is the next point of the current coarse arc's
interpolant, including the closing step at the end of a block. -/
theorem quittingUniformMeshValue_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {m : ℕ} (hm : 0 < m)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (time : ℕ) :
    quittingUniformMeshValue reward owner mass value m (time + 1) =
      let coarse := quittingUniformMeshCoarseTime m time
      quittingMeshPayoffInterpolant
        (quittingSoloReward reward (owner coarse))
        (value coarse)
        (1 - quittingMeshHazard (mass coarse) m)
        (quittingUniformMeshOffset m time + 1) := by
  let coarse := quittingUniformMeshCoarseTime m time
  let offset := quittingUniformMeshOffset m time
  have hoffset : offset < m := by
    exact quittingUniformMeshOffset_lt hm
  have hdecompose : offset + m * coarse = time := by
    dsimp only [offset, coarse, quittingUniformMeshOffset,
      quittingUniformMeshCoarseTime]
    exact Nat.mod_add_div time m
  by_cases hinside : offset + 1 < m
  · have hcoarseSucc :
        quittingUniformMeshCoarseTime m (time + 1) = coarse := by
      dsimp only [quittingUniformMeshCoarseTime]
      calc
        (time + 1) / m = (offset + 1 + m * coarse) / m := by
          rw [← hdecompose]
          congr 1
          ac_rfl
        _ = (offset + 1) / m + coarse :=
          Nat.add_mul_div_left (offset + 1) coarse hm
        _ = coarse := by rw [Nat.div_eq_of_lt hinside, zero_add]
    have hoffsetSucc :
        quittingUniformMeshOffset m (time + 1) = offset + 1 := by
      dsimp only [quittingUniformMeshOffset]
      calc
        (time + 1) % m = (offset + 1 + m * coarse) % m := by
          rw [← hdecompose]
          congr 1
          ac_rfl
        _ = (offset + 1) % m := Nat.add_mul_mod_self_left _ _ _
        _ = offset + 1 := Nat.mod_eq_of_lt hinside
    unfold quittingUniformMeshValue
    rw [hcoarseSucc, hoffsetSucc]
  · have hlast : offset + 1 = m := by omega
    have htimeSucc : time + 1 = m * (coarse + 1) := by
      calc
        time + 1 = offset + m * coarse + 1 := by rw [hdecompose]
        _ = (offset + 1) + m * coarse := by omega
        _ = m + m * coarse := by rw [hlast]
        _ = m * (coarse + 1) := by ring
    have hcoarseSucc :
        quittingUniformMeshCoarseTime m (time + 1) = coarse + 1 := by
      dsimp only [quittingUniformMeshCoarseTime]
      rw [htimeSucc, Nat.mul_comm, Nat.mul_div_left _ hm]
    have hoffsetSucc :
        quittingUniformMeshOffset m (time + 1) = 0 := by
      dsimp only [quittingUniformMeshOffset]
      rw [htimeSucc, Nat.mul_comm, Nat.mul_mod_left]
    calc
      quittingUniformMeshValue reward owner mass value m (time + 1) =
          value (coarse + 1) := by
            unfold quittingUniformMeshValue
            rw [hcoarseSucc, hoffsetSucc]
            exact quittingMeshPayoffInterpolant_zero _ _ _
      _ = quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) m) m := by
            symm
            exact quittingMeshPayoffInterpolant_at_length_eq_next
              (hmass1 coarse) hm (harc coarse)
      _ = quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) m) (offset + 1) := by
            rw [hlast]

/-- A uniform micro-hazard is nonnegative. -/
theorem quittingUniformMeshMass_nonneg
    (mass : ℕ → ℝ) (m : ℕ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1) :
    ∀ time, 0 ≤ quittingUniformMeshMass mass m time := by
  intro time
  exact quittingMeshHazard_nonneg m
    (hmass0 (quittingUniformMeshCoarseTime m time))
    (hmass1 (quittingUniformMeshCoarseTime m time))

/-- A uniform micro-hazard is at most one. -/
theorem quittingUniformMeshMass_le_one
    (mass : ℕ → ℝ) (m : ℕ)
    (hmass1 : ∀ time, mass time ≤ 1) :
    ∀ time, quittingUniformMeshMass mass m time ≤ 1 := by
  intro time
  exact quittingMeshHazard_le_one m
    (hmass1 (quittingUniformMeshCoarseTime m time))

/-- Product singleton roots implementing the uniformly subdivided path. -/
def quittingUniformMeshRoots
    [Fintype ι] [DecidableEq ι]
    (owner : ℕ → ι) (mass : ℕ → ℝ) (m : ℕ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1) :
    ℕ → ι → PMF Bool :=
  quittingEssentialAPSSingletonRoots
    (quittingUniformMeshOwner owner m)
    (quittingUniformMeshMass mass m)
    (quittingUniformMeshMass_nonneg mass m hmass0 hmass1)
    (quittingUniformMeshMass_le_one mass m hmass1)

/-! ## Interpolated viability and bounds -/

/-- Upper-bound counterpart of
`le_quittingMeshPayoffInterpolant_of_arcEndpoints`. -/
theorem quittingMeshPayoffInterpolant_le_of_arcEndpoints
    {p : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hm : 0 < m)
    {root start next upper : Payoff ι}
    (harc : start = quittingSingletonArcPayoff p root next)
    (hupperStart : ∀ who, start who ≤ upper who)
    (hupperNext : ∀ who, next who ≤ upper who)
    (k : ℕ) (hk : k ≤ m) (who : ι) :
    quittingMeshPayoffInterpolant root start
        (1 - quittingMeshHazard p m) k who ≤ upper who := by
  let q := 1 - quittingMeshHazard p m
  have hqpos : 0 < q := by
    dsimp only [q]
    rw [one_sub_quittingMeshHazard]
    exact Real.rpow_pos_of_pos (sub_pos.mpr hp1) _
  have hqle : q ≤ 1 := by
    dsimp only [q]
    have hhazard := quittingMeshHazard_nonneg m hp0 hp1.le
    linarith
  have hqpow : q ^ m = 1 - p := by
    dsimp only [q]
    exact one_sub_quittingMeshHazard_pow hp1.le hm
  have harcWho : start who =
      p * root who + (1 - p) * next who := by
    simpa [quittingSingletonArcPayoff] using congrFun harc who
  have hstart : start who =
      root who + q ^ m * (next who - root who) := by
    rw [hqpow, harcWho]
    ring
  have hform := quittingMeshInterpolant_eq_pow_sub
    hqpos.ne' hk hstart
  rw [quittingMeshPayoffInterpolant_apply, hform]
  have hpowerLower : q ^ m ≤ q ^ (m - k) :=
    pow_le_pow_of_le_one hqpos.le hqle (Nat.sub_le m k)
  have hpowerUpper : q ^ (m - k) ≤ 1 :=
    pow_le_one₀ hqpos.le hqle
  by_cases hdirection : 0 ≤ next who - root who
  · have hscaled := mul_le_mul_of_nonneg_right hpowerUpper hdirection
    calc
      root who + q ^ (m - k) * (next who - root who) ≤
          root who + 1 * (next who - root who) :=
        add_le_add (le_refl _) hscaled
      _ = next who := by ring
      _ ≤ upper who := hupperNext who
  · have hscaled := mul_le_mul_of_nonpos_right
      hpowerLower (le_of_not_ge hdirection)
    calc
      root who + q ^ (m - k) * (next who - root who) ≤
          root who + q ^ m * (next who - root who) :=
        add_le_add (le_refl _) hscaled
      _ = start who := hstart.symm
      _ ≤ upper who := hupperStart who

/-- A common absolute bound on both coarse endpoints bounds every interpolated
micro-value. -/
theorem abs_quittingMeshPayoffInterpolant_le_of_arcEndpoints
    {p bound : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hm : 0 < m)
    {root start next : Payoff ι}
    (harc : start = quittingSingletonArcPayoff p root next)
    (hstartBound : ∀ who, |start who| ≤ bound)
    (hnextBound : ∀ who, |next who| ≤ bound)
    (k : ℕ) (hk : k ≤ m) (who : ι) :
    |quittingMeshPayoffInterpolant root start
        (1 - quittingMeshHazard p m) k who| ≤ bound := by
  rw [abs_le]
  constructor
  · apply le_quittingMeshPayoffInterpolant_of_arcEndpoints
      (root := root) (start := start) (next := next) (lower := fun _ => -bound)
      hp0 hp1 hm harc
    · intro player
      exact (abs_le.mp (hstartBound player)).1
    · intro player
      exact (abs_le.mp (hnextBound player)).1
    · exact hk
  · apply quittingMeshPayoffInterpolant_le_of_arcEndpoints
      hp0 hp1 hm harc
    · intro player
      exact (abs_le.mp (hstartBound player)).2
    · intro player
      exact (abs_le.mp (hnextBound player)).2
    · exact hk

/-- Viability of both coarse endpoints is inherited by every micro-value. -/
theorem quittingUniformMeshValue_viable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {m : ℕ} (hm : 0 < m)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hviable : ∀ time, QuittingEssentialAPSViable reward (value time)) :
    ∀ time, QuittingEssentialAPSViable reward
      (quittingUniformMeshValue reward owner mass value m time) := by
  intro time who
  let coarse := quittingUniformMeshCoarseTime m time
  let offset := quittingUniformMeshOffset m time
  have hoffset : offset ≤ m :=
    (quittingUniformMeshOffset_lt hm).le
  unfold quittingUniformMeshValue
  exact le_quittingMeshPayoffInterpolant_of_arcEndpoints
    (hmass0 coarse) (hmass1 coarse) hm (harc coarse)
    (hviable coarse) (hviable (coarse + 1)) offset hoffset who

/-- Bounded coarse values give the same bound on every micro-value. -/
theorem quittingUniformMeshValue_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {m : ℕ} (hm : 0 < m)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    {bound : ℝ} (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    ∀ time who,
      |quittingUniformMeshValue reward owner mass value m time who| ≤ bound := by
  intro time who
  let coarse := quittingUniformMeshCoarseTime m time
  let offset := quittingUniformMeshOffset m time
  have hoffset : offset ≤ m :=
    (quittingUniformMeshOffset_lt hm).le
  unfold quittingUniformMeshValue
  exact abs_quittingMeshPayoffInterpolant_le_of_arcEndpoints
    (hmass0 coarse) (hmass1 coarse) hm (harc coarse)
    (hvalueBound coarse) (hvalueBound (coarse + 1)) offset hoffset who

/-- The active coordinate stays pinned throughout its whole microblock. -/
theorem quittingUniformMeshValue_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (m time : ℕ)
    (hactive : ∀ coarse,
      value coarse (owner coarse) =
        quittingSoloReward reward (owner coarse) (owner coarse)) :
    quittingUniformMeshValue reward owner mass value m time
        (quittingUniformMeshOwner owner m time) =
      quittingSoloReward reward
        (quittingUniformMeshOwner owner m time)
        (quittingUniformMeshOwner owner m time) := by
  unfold quittingUniformMeshValue quittingUniformMeshOwner
  exact quittingMeshPayoffInterpolant_eq_root_of_eq
    (hactive (quittingUniformMeshCoarseTime m time)) _

end GameTheory
