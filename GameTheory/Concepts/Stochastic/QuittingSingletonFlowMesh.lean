/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCyclicSupersolution

/-!
# Singleton-flow subdivision meshes

A coarse singleton-flow hazard `p` is subdivided into `m` identical hazards

`h(p,m) = 1 - (1 - p) ^ (1 / m)`.

The continue probability over the `m` microstages is exactly `1 - p`.  If
`a = -log (1-p)`, then `h(p,m) ≤ a / m`.  These facts feed the cyclic
quit-only-error supersolution compiler without geometrically accumulating
the local error.

The capstone in this file is horizon-indexed: its mesh scale `m`, cycle, and
behavior profile may depend on the horizon `N`.  It does not assert that one
fixed strategy works at every horizon.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {L m : ℕ} {ι : Type}

/-! ## Exact hazard subdivision -/

/-- Microstage hazard whose `m`-fold continue probability is `1 - p`. -/
def quittingMeshHazard (p : ℝ) (m : ℕ) : ℝ :=
  1 - (1 - p) ^ ((m : ℝ)⁻¹ : ℝ)

/-- Logarithmic intensity of a coarse hazard. -/
def quittingMeshIntensity (p : ℝ) : ℝ :=
  -Real.log (1 - p)

theorem quittingMeshIntensity_nonneg {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ quittingMeshIntensity p := by
  unfold quittingMeshIntensity
  exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))

theorem quittingMeshHazard_nonneg {p : ℝ} (m : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ quittingMeshHazard p m := by
  unfold quittingMeshHazard
  exact sub_nonneg.mpr
    (Real.rpow_le_one (by linarith) (by linarith) (by positivity))

theorem quittingMeshHazard_le_one {p : ℝ} (m : ℕ)
    (hp1 : p ≤ 1) :
    quittingMeshHazard p m ≤ 1 := by
  unfold quittingMeshHazard
  exact sub_le_self _ (Real.rpow_nonneg (by linarith) _)

@[simp] theorem one_sub_quittingMeshHazard (p : ℝ) (m : ℕ) :
    1 - quittingMeshHazard p m =
      (1 - p) ^ ((m : ℝ)⁻¹ : ℝ) := by
  simp [quittingMeshHazard]

/-- Exact subdivision: `m` microstage continue probabilities multiply to
the original coarse continue probability. -/
theorem one_sub_quittingMeshHazard_pow {p : ℝ} {m : ℕ}
    (hp1 : p ≤ 1) (hm : 0 < m) :
    (1 - quittingMeshHazard p m) ^ m = 1 - p := by
  rw [one_sub_quittingMeshHazard, ← Real.rpow_natCast,
    ← Real.rpow_mul (by linarith)]
  have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [inv_mul_cancel₀ hmReal, Real.rpow_one]

/-- Exponential form of the subdivided hazard. -/
theorem quittingMeshHazard_eq_one_sub_exp {p : ℝ} {m : ℕ}
    (hp1 : p < 1) :
    quittingMeshHazard p m =
      1 - Real.exp (-(quittingMeshIntensity p / (m : ℝ))) := by
  have hbase : 0 < 1 - p := sub_pos.mpr hp1
  unfold quittingMeshHazard quittingMeshIntensity
  rw [Real.rpow_def_of_pos hbase]
  congr 2
  ring

/-- The microstage hazard is at most logarithmic intensity divided by the
subdivision count. -/
theorem quittingMeshHazard_le_intensity_div {p : ℝ} {m : ℕ}
    (hp1 : p < 1) :
    quittingMeshHazard p m ≤ quittingMeshIntensity p / (m : ℝ) := by
  rw [quittingMeshHazard_eq_one_sub_exp hp1]
  have hexp := Real.one_sub_le_exp_neg
    (quittingMeshIntensity p / (m : ℝ))
  linarith

/-- Uniform intensity bound for a finite family of coarse hazards. -/
theorem quittingMeshHazard_le_intensityBound_div
    (p : Fin L → ℝ) {m : ℕ} {aStar : ℝ}
    (hp1 : ∀ ell, p ell < 1)
    (ha : ∀ ell, quittingMeshIntensity (p ell) ≤ aStar)
    (ell : Fin L) :
    quittingMeshHazard (p ell) m ≤ aStar / (m : ℝ) := by
  exact (quittingMeshHazard_le_intensity_div (hp1 ell)).trans
    (div_le_div_of_nonneg_right (ha ell) (Nat.cast_nonneg m))

/-! ## Arc interpolation -/

/-- Scalar interpolation along one subdivided singleton-flow arc.  At
microstage `k`, the displacement from the active singleton payoff `root` is
the initial displacement divided by `a ^ k`. -/
def quittingMeshInterpolant
    (root start a : ℝ) (k : ℕ) : ℝ :=
  root + (a ^ k)⁻¹ * (start - root)

/-- One interpolation step is exactly the Bellman mixture with continue
probability `a`. -/
theorem quittingMeshInterpolant_eq_mix_succ
    {root start a : ℝ} (ha : a ≠ 0) (k : ℕ) :
    quittingMeshInterpolant root start a k =
      (1 - a) * root +
        a * quittingMeshInterpolant root start a (k + 1) := by
  unfold quittingMeshInterpolant
  field_simp [pow_succ, ha]
  all_goals ring

/-- Payoff-vector version of the arc interpolation, applied coordinatewise. -/
def quittingMeshPayoffInterpolant
    (root start : Payoff ι) (a : ℝ) (k : ℕ) : Payoff ι :=
  fun who ↦ quittingMeshInterpolant (root who) (start who) a k

@[simp] theorem quittingMeshPayoffInterpolant_apply
    (root start : Payoff ι) (a : ℝ) (k : ℕ) (who : ι) :
    quittingMeshPayoffInterpolant root start a k who =
      quittingMeshInterpolant (root who) (start who) a k := rfl

/-- Vector Bellman transport along one microstage of an arc. -/
theorem quittingMeshPayoffInterpolant_eq_mix_succ
    {root start : Payoff ι} {a : ℝ} (ha : a ≠ 0) (k : ℕ) :
    quittingMeshPayoffInterpolant root start a k =
      fun who ↦ (1 - a) * root who +
        a * quittingMeshPayoffInterpolant root start a (k + 1) who := by
  funext who
  exact quittingMeshInterpolant_eq_mix_succ ha k

/-- The interpolated value of a coordinate fixed at the active singleton
payoff stays constant throughout the whole microblock. -/
theorem quittingMeshPayoffInterpolant_eq_root_of_eq
    {root start : Payoff ι} {a : ℝ} {who : ι}
    (hactive : start who = root who) (k : ℕ) :
    quittingMeshPayoffInterpolant root start a k who = root who := by
  simp [quittingMeshPayoffInterpolant, quittingMeshInterpolant, hactive]

/-- Coarse arc equation
`start = p · root + (1-p) · next`, written pointwise. -/
def quittingSingletonArcPayoff
    (p : ℝ) (root next : Payoff ι) : Payoff ι :=
  fun who ↦ p * root who + (1 - p) * next who

/-- The logarithmic subdivision instantiates the abstract interpolation step:
the microstage stopping probability is exactly `quittingMeshHazard p m`. -/
theorem quittingMeshPayoffInterpolant_hazard_step
    {p : ℝ} (hp1 : p < 1) (root start : Payoff ι)
    (m k : ℕ) :
    quittingMeshPayoffInterpolant root start
        (1 - quittingMeshHazard p m) k =
      fun who ↦
        quittingMeshHazard p m * root who +
          (1 - quittingMeshHazard p m) *
            quittingMeshPayoffInterpolant root start
              (1 - quittingMeshHazard p m) (k + 1) who := by
  have ha : 1 - quittingMeshHazard p m ≠ 0 := by
    rw [one_sub_quittingMeshHazard]
    exact ne_of_gt (Real.rpow_pos_of_pos (sub_pos.mpr hp1) _)
  rw [quittingMeshPayoffInterpolant_eq_mix_succ ha]
  funext who
  ring

/-- The final interpolated microstage closes exactly at the next coarse value
when the coarse endpoints satisfy the singleton-flow arc equation. -/
theorem quittingMeshPayoffInterpolant_at_length_eq_next
    {p : ℝ} {m : ℕ} (hp1 : p < 1) (hm : 0 < m)
    {root start next : Payoff ι}
    (harc : start = quittingSingletonArcPayoff p root next) :
    quittingMeshPayoffInterpolant root start
        (1 - quittingMeshHazard p m) m = next := by
  funext who
  have harcWho : start who =
      p * root who + (1 - p) * next who := by
    simpa [quittingSingletonArcPayoff] using congrFun harc who
  simp only [quittingMeshPayoffInterpolant_apply]
  unfold quittingMeshInterpolant
  rw [one_sub_quittingMeshHazard_pow hp1.le hm, harcWho]
  have hcontinue : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  field_simp [hcontinue]
  all_goals ring

/-! ## Local quit slack -/

/-- If quitting alone is no better than the live value, mixing in a collision
with probability `h` costs at most `h` times the positive collision surplus. -/
theorem singletonQuitMix_le_value_add_hazard_mul_posPart
    {h solo collision current : ℝ}
    (hh : 0 ≤ h) (hsolo : solo ≤ current) :
    (1 - h) * solo + h * collision ≤
      current + h * max (collision - solo) 0 := by
  have hgap : collision - solo ≤ max (collision - solo) 0 :=
    le_max_left _ _
  have hscaled := mul_le_mul_of_nonneg_left hgap hh
  calc
    (1 - h) * solo + h * collision =
        solo + h * (collision - solo) := by ring
    _ ≤ current + h * max (collision - solo) 0 :=
      add_le_add hsolo hscaled

/-- A uniform bound on the positive collision surplus yields the local
`h * D` quit-error hypothesis consumed by the cyclic supersolution theorem. -/
theorem singletonQuitMix_le_value_add_hazard_mul
    {h solo collision current D : ℝ}
    (hh : 0 ≤ h) (hsolo : solo ≤ current)
    (hgap : max (collision - solo) 0 ≤ D) :
    (1 - h) * solo + h * collision ≤ current + h * D := by
  exact (singletonQuitMix_le_value_add_hazard_mul_posPart hh hsolo).trans
    (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left hgap hh))

/-! ## Canonical `L × m` phase indexing -/

/-- Coarse singleton-flow block containing a microphase of an `L * m`
cycle. -/
def quittingSingletonMeshBlock (phase : Fin (L * m)) : Fin L :=
  (finProdFinEquiv.symm phase).1

/-- Microstage offset inside the coarse singleton-flow block. -/
def quittingSingletonMeshOffset (phase : Fin (L * m)) : Fin m :=
  (finProdFinEquiv.symm phase).2

/-! ## Canonical square-root scale and cycle budget -/

/-- Integer mesh scale selected at horizon `N`. -/
def quittingSqrtMeshScale (N : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (N : ℝ))

/-- At every positive horizon, `ceil (sqrt N)` is a positive integer between
`sqrt N` and `2 sqrt N`. -/
theorem quittingSqrtMeshScale_spec {N : ℕ} (hN : 1 ≤ (N : ℝ)) :
    0 < quittingSqrtMeshScale N ∧
      Real.sqrt (N : ℝ) ≤ (quittingSqrtMeshScale N : ℝ) ∧
      (quittingSqrtMeshScale N : ℝ) ≤
        2 * Real.sqrt (N : ℝ) := by
  have hN0 : 0 ≤ (N : ℝ) := le_trans (by norm_num) hN
  have hsqrt1 : 1 ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sq_sqrt hN0, Real.sqrt_nonneg (N : ℝ)]
  have hsqrt0 : 0 < Real.sqrt (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one hsqrt1
  constructor
  · rw [quittingSqrtMeshScale, Nat.ceil_pos]
    exact hsqrt0
  constructor
  · exact Nat.le_ceil _
  · unfold quittingSqrtMeshScale
    have hceilLt : ((Nat.ceil (Real.sqrt (N : ℝ)) : ℕ) : ℝ) <
        Real.sqrt (N : ℝ) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg (N : ℝ))
    linarith

/-- A uniform bound on each opponent's one-cycle continuation product gives
the cycle-gap budget with the explicit constant `L / (1-rhoBar)`. -/
theorem quittingSingletonMesh_cycleBudget_of_product_le
    [Fintype ι] [DecidableEq ι]
    (cycle : Fin (L * m) → ι → PMF Bool)
    {rhoBar : ℝ} (hrho : rhoBar < 1)
    (hprod : ∀ who,
      (∏ cyclePhase : Fin (L * m),
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) ≤ rhoBar) :
    ∀ who,
      ((L * m : ℕ) : ℝ) /
          (1 - ∏ cyclePhase : Fin (L * m),
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) who) ≤
        ((L : ℝ) / (1 - rhoBar)) * (m : ℝ) := by
  intro who
  let rhoWho := ∏ cyclePhase : Fin (L * m),
    quittingStationaryFixedOpponentsContinueMass
      (cycle cyclePhase) who
  have hden : 1 - rhoBar ≤ 1 - rhoWho := by
    dsimp only [rhoWho]
    linarith [hprod who]
  have hden0 : 0 < 1 - rhoBar := sub_pos.mpr hrho
  have hnum0 : 0 ≤ ((L * m : ℕ) : ℝ) := by positivity
  calc
    ((L * m : ℕ) : ℝ) / (1 - rhoWho) ≤
        ((L * m : ℕ) : ℝ) / (1 - rhoBar) :=
      div_le_div_of_nonneg_left hnum0 hden0 hden
    _ = ((L : ℝ) / (1 - rhoBar)) * (m : ℝ) := by
      push_cast
      ring

/-! ## Horizon-indexed singleton-flow consumer -/

/-- **Horizon-indexed singleton-flow mesh compiler.**

The cycle has exactly `K = L * m` microphases.  Prescribed policy evaluation
and prescribed Continue are exact.  The only local exploitability is the
Quit endpoint error `D * h_{ℓ,m}`.  Bounded logarithmic intensities turn this
into the global terminal error `D * aStar / m` through the cyclic
supersolution theorem, with no `K`-fold accumulation.  The cycle-gap budget
then supplies the explicit finite-horizon boundary and the square-root rate.

The selected initial phase delivers the fixed vector `w0`; both Nash and
delivery conclusions concern this one supplied horizon `N`. -/
theorem singletonFlowMesh_isSqrtRateHorizonNash_and_delivers
    [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (p : Fin L → ℝ)
    (cycle : Fin (L * m) → ι → PMF Bool)
    (value : Fin (L * m) → Payoff ι)
    (phase : Fin (L * m)) (w0 : Payoff ι)
    {N : ℕ} {aStar D C bound : ℝ}
    (hm : 0 < m)
    (hp0 : ∀ ell, 0 ≤ p ell) (hp1 : ∀ ell, p ell < 1)
    (ha : ∀ ell, quittingMeshIntensity (p ell) ≤ aStar)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hbound : 0 ≤ bound)
    (hN : 1 ≤ (N : ℝ))
    (hm_lower : Real.sqrt (N : ℝ) ≤ (m : ℝ))
    (hm_upper : (m : ℝ) ≤ 2 * Real.sqrt (N : ℝ))
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate (L * m) cyclePhase)) (cycle cyclePhase))
    (hcontinue : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsContinueReward
          reward (cycle cyclePhase) who +
        quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) who *
          value (finRotate (L * m) cyclePhase) who = value cyclePhase who)
    (hquit : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsQuitValue
          reward (cycle cyclePhase) who ≤
        value cyclePhase who +
          D * quittingMeshHazard
            (p (quittingSingletonMeshBlock cyclePhase)) m)
    (hcontracts : ∀ who,
      (∏ cyclePhase : Fin (L * m),
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1)
    (hcycleBudget : ∀ who,
      ((L * m : ℕ) : ℝ) / (1 - ∏ cyclePhase : Fin (L * m),
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) who) ≤ C * (m : ℝ))
    (hvaluePhase : value phase = w0) :
    (quittingGame reward).IsεHorizonNash none N
        ((D * aStar + 4 * bound * C) / Real.sqrt (N : ℝ))
        (quittingCyclicBehaviorProfile reward cycle phase) ∧
      ∀ who,
        |(quittingGame reward).finiteAveragePayoff none N
            (quittingCyclicBehaviorProfile reward cycle phase) who - w0 who| ≤
          (2 * bound * C) / Real.sqrt (N : ℝ) := by
  let terminalError := D * aStar / (m : ℝ)
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  let boundaryError := bound * (C * (m : ℝ) / (N : ℝ))
  have haStar : 0 ≤ aStar :=
    (quittingMeshIntensity_nonneg
      (hp0 (quittingSingletonMeshBlock phase))
      (hp1 (quittingSingletonMeshBlock phase)).le).trans
        (ha (quittingSingletonMeshBlock phase))
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hNReal : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN
  have hNpositive : 0 < N := by exact_mod_cast hNReal
  have hterminalError0 : 0 ≤ terminalError := by
    exact div_nonneg (mul_nonneg hD haStar) hmReal.le
  have hquitUniform : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsQuitValue
          reward (cycle cyclePhase) who ≤
        value cyclePhase who + terminalError := by
    intro cyclePhase who
    have hhazard := quittingMeshHazard_le_intensityBound_div
      (m := m) p hp1 ha (quittingSingletonMeshBlock cyclePhase)
    have hscaled := mul_le_mul_of_nonneg_left hhazard hD
    have hlocal := hquit cyclePhase who
    dsimp only [terminalError]
    calc
      quittingStationaryFixedOpponentsQuitValue
          reward (cycle cyclePhase) who ≤
          value cyclePhase who +
            D * quittingMeshHazard
              (p (quittingSingletonMeshBlock cyclePhase)) m := hlocal
      _ ≤ value cyclePhase who + D * (aStar / (m : ℝ)) :=
        add_le_add (le_refl _) hscaled
      _ = value cyclePhase who + D * aStar / (m : ℝ) := by ring
  have hterminalNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) terminalError profile := by
    exact
      isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue
        reward cycle value phase hterminalError0 hbound hreward
        hpolicy hquitUniform hcontinue hcontracts
  have hsurvival : ∀ who,
      quittingOpponentLiveCesaro reward profile who N ≤
        C * (m : ℝ) / (N : ℝ) := by
    intro who
    have hclock :=
      quittingOpponentLiveCesaro_cyclicBehaviorProfile_le
        reward cycle phase who N (hcontracts who)
    have hscaled :
        (((L * m : ℕ) : ℝ) /
            (1 - ∏ cyclePhase : Fin (L * m),
              quittingStationaryFixedOpponentsContinueMass
                (cycle cyclePhase) who)) / (N : ℝ) ≤
          C * (m : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right (hcycleBudget who) hNReal.le
    simpa only [profile] using hclock.trans hscaled
  have hdeliveryTerminal : ∀ who,
      |(quittingGame reward).finiteAveragePayoff none N profile who -
        quittingTerminalPayoff reward profile who| ≤ boundaryError := by
    intro who
    have htail :=
      abs_finiteAveragePayoff_sub_terminal_le_opponentLiveCesaro
        reward profile who N hNpositive bound hbound
          (fun terminal ↦ hreward terminal who)
    have hscaled := mul_le_mul_of_nonneg_left (hsurvival who) hbound
    simpa only [boundaryError] using htail.trans hscaled
  have hdeviation : ∀ who
      (deviation : (quittingGame reward).BehaviorStrategy who),
      (quittingGame reward).finiteAveragePayoff none N
          (Function.update profile who deviation) who ≤
        quittingTerminalPayoff reward
            (Function.update profile who deviation) who + boundaryError := by
    intro who deviation
    have hfinite :=
      finiteAveragePayoff_update_le_terminal_add_opponentLiveCesaro'
        reward profile who deviation N hNpositive bound hbound
          (fun terminal ↦ hreward terminal who)
    have hscaled := mul_le_mul_of_nonneg_left (hsurvival who) hbound
    exact hfinite.trans
      (add_le_add (le_refl _) (by simpa only [boundaryError] using hscaled))
  have hfiniteNash :=
    hterminalNash.isεHorizonNash_of_explicitBounds
      hdeliveryTerminal hdeviation
  have hrate : terminalError + boundaryError + boundaryError ≤
      (D * aStar + 4 * bound * C) / Real.sqrt (N : ℝ) := by
    have hscalar := inv_add_linear_le_sqrt_rate
      (A := D * aStar) (B := 2 * bound * C)
      (N := (N : ℝ)) (m := (m : ℝ))
      (mul_nonneg hD haStar)
      (mul_nonneg (mul_nonneg (by norm_num) hbound) hC)
      hN hm_lower hm_upper
    calc
      terminalError + boundaryError + boundaryError =
          (D * aStar) / (m : ℝ) +
            (2 * bound * C) * (m : ℝ) / (N : ℝ) := by
              dsimp only [terminalError, boundaryError]
              ring
      _ ≤ (D * aStar + 2 * (2 * bound * C)) /
          Real.sqrt (N : ℝ) := hscalar
      _ = (D * aStar + 4 * bound * C) /
          Real.sqrt (N : ℝ) := by ring
  constructor
  · exact hfiniteNash.mono hrate
  · intro who
    have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
      reward cycle value hpolicy hcontracts
    have hterminalEq : quittingTerminalPayoff reward profile who = w0 who := by
      dsimp only [profile]
      rw [quittingTerminalPayoff_cyclicBehaviorProfile, ← hvalue,
        hvaluePhase]
    have hdeliveryW0 :
        |(quittingGame reward).finiteAveragePayoff none N profile who -
          w0 who| ≤ boundaryError := by
      rw [← hterminalEq]
      exact hdeliveryTerminal who
    have hboundaryRate : boundaryError ≤
        (2 * bound * C) / Real.sqrt (N : ℝ) := by
      have hscalar := inv_add_linear_le_sqrt_rate
        (A := 0) (B := bound * C) (N := (N : ℝ)) (m := (m : ℝ))
        (by norm_num) (mul_nonneg hbound hC) hN hm_lower hm_upper
      dsimp only [boundaryError]
      calc
        bound * (C * (m : ℝ) / (N : ℝ)) =
            (bound * C) * (m : ℝ) / (N : ℝ) := by ring
        _ ≤ (0 + 2 * (bound * C)) / Real.sqrt (N : ℝ) := by
          simpa only [zero_div, zero_add] using hscalar
        _ = (2 * bound * C) / Real.sqrt (N : ℝ) := by ring
    exact hdeliveryW0.trans hboundaryRate

/-- **Canonical game-facing singleton-flow compiler.**

This corollary chooses `m_N = ceil (sqrt N)` itself and replaces the abstract
cycle-gap budget by the explicit hypothesis that every opponent's one-cycle
continuation product is at most `rhoBar < 1`.  Thus the boundary constant is
the visible quantity `L / (1-rhoBar)`.  The cycle and values remain
horizon-indexed data at this canonical scale. -/
theorem singletonFlowSqrtMesh_isHorizonNash_and_delivers_of_product_le
    [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {N : ℕ} (p : Fin L → ℝ)
    (cycle : Fin (L * quittingSqrtMeshScale N) → ι → PMF Bool)
    (value : Fin (L * quittingSqrtMeshScale N) → Payoff ι)
    (phase : Fin (L * quittingSqrtMeshScale N)) (w0 : Payoff ι)
    {aStar D rhoBar bound : ℝ}
    (hp0 : ∀ ell, 0 ≤ p ell) (hp1 : ∀ ell, p ell < 1)
    (ha : ∀ ell, quittingMeshIntensity (p ell) ≤ aStar)
    (hD : 0 ≤ D) (hrho : rhoBar < 1) (hbound : 0 ≤ bound)
    (hN : 1 ≤ (N : ℝ))
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hpolicy : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
        (value (finRotate (L * quittingSqrtMeshScale N) cyclePhase))
        (cycle cyclePhase))
    (hcontinue : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsContinueReward
          reward (cycle cyclePhase) who +
        quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) who *
          value
            (finRotate (L * quittingSqrtMeshScale N) cyclePhase) who =
        value cyclePhase who)
    (hquit : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsQuitValue
          reward (cycle cyclePhase) who ≤
        value cyclePhase who +
          D * quittingMeshHazard
            (p (quittingSingletonMeshBlock cyclePhase))
            (quittingSqrtMeshScale N))
    (hprod : ∀ who,
      (∏ cyclePhase : Fin (L * quittingSqrtMeshScale N),
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) ≤ rhoBar)
    (hvaluePhase : value phase = w0) :
    (quittingGame reward).IsεHorizonNash none N
        ((D * aStar +
            4 * bound * ((L : ℝ) / (1 - rhoBar))) /
          Real.sqrt (N : ℝ))
        (quittingCyclicBehaviorProfile reward cycle phase) ∧
      ∀ who,
        |(quittingGame reward).finiteAveragePayoff none N
            (quittingCyclicBehaviorProfile reward cycle phase) who - w0 who| ≤
          (2 * bound * ((L : ℝ) / (1 - rhoBar))) /
            Real.sqrt (N : ℝ) := by
  have hmesh := quittingSqrtMeshScale_spec hN
  have hcontracts : ∀ who,
      (∏ cyclePhase : Fin (L * quittingSqrtMeshScale N),
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 := by
    intro who
    exact (hprod who).trans_lt hrho
  have hC : 0 ≤ (L : ℝ) / (1 - rhoBar) :=
    div_nonneg (Nat.cast_nonneg L) (sub_pos.mpr hrho).le
  have hcycleBudget :=
    quittingSingletonMesh_cycleBudget_of_product_le
      (L := L) (m := quittingSqrtMeshScale N)
      cycle hrho hprod
  exact singletonFlowMesh_isSqrtRateHorizonNash_and_delivers
    (L := L) (m := quittingSqrtMeshScale N) (N := N)
    reward p cycle value phase w0
    hmesh.1 hp0 hp1 ha hD hC hbound hN hmesh.2.1 hmesh.2.2
    hreward hpolicy hcontinue hquit hcontracts hcycleBudget hvaluePhase

end GameTheory
