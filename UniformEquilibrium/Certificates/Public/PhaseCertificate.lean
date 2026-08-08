/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.Certificates.Adaptive.Certificate

/-!
# Public-phase equilibrium certificates

A public-phase strategy reads a phase from the observed finite history and
uses that phase both to choose the current mixed action profile and to index
continuation potentials.  This is the proof-facing form of strategies built
from calendars, accounts, regimes, and punishment modes.

`IsPublicPhasePunishmentSystemAt` is a local certificate.  Its hypotheses are
historywise one-step inequalities, including after every unilateral behavior
deviation.  The main theorem in this file compiles those local inequalities
into `IsAdaptivePotentialCertificateAt`, whose hypotheses are stated only
after averaging over the induced history laws.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type}

/-- A strategy whose publicly observable phase determines current play.

The phase may retain any public memory extracted from the finite history.
In applications it can be a finite controller state, an account level, a
calendar regime, or a product of these data. -/
structure PublicPhaseProfile (G : StochasticGame ι) where
  Phase : Type
  phase : (t : ℕ) → G.Hist t → Phase
  play : Phase → ∀ i, PMF (G.Act i)

namespace PublicPhaseProfile

/-- The behavior profile induced by public-phase play. -/
def behaviorProfile (P : PublicPhaseProfile G) : G.BehaviorProfile :=
  fun i t h => P.play (P.phase t h) i

/-- A phase-indexed scalar, read as a history potential along `P`. -/
def historyPotential (P : PublicPhaseProfile G) (w : P.Phase → ℝ) :
    G.HistoryPotential :=
  fun t h => w (P.phase t h)

end PublicPhaseProfile

/-- Local public-phase data sufficient for an adaptive potential certificate.

The three potentials and their charges are deliberately separate: lower and
upper control recommended play, while deviation controls every unilateral
behavior deviation.  Each one-step condition is required before averaging,
at every public history. -/
structure PublicPhasePunishmentSystemAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (P : PublicPhaseProfile G) (s₀ : G.State) (v : Payoff ι) (δ : ℝ) where
  horizon : ℕ
  lowerPotential : ι → P.Phase → ℝ
  upperPotential : ι → P.Phase → ℝ
  deviationPotential : ι → P.Phase → ℝ
  lowerCharge : ι → G.HistoryPotential
  upperCharge : ι → G.HistoryPotential
  deviationCharge : ∀ i, G.BehaviorStrategy i → G.HistoryPotential
  horizon_ge_two : 2 ≤ horizon
  lower_initial : ∀ i,
    |lowerPotential i (P.phase 0 (G.emptyHist s₀)) - v i| ≤ δ
  upper_initial : ∀ i,
    |upperPotential i (P.phase 0 (G.emptyHist s₀)) - v i| ≤ δ
  deviation_initial : ∀ i,
    |deviationPotential i (P.phase 0 (G.emptyHist s₀)) - v i| ≤ δ
  lower_subharmonic : ∀ i (t : ℕ) (h : G.Hist t),
    P.historyPotential (lowerPotential i) t h ≤
      G.historyContinuationEU P.behaviorProfile
        (P.historyPotential (lowerPotential i)) h
  lower_stage : ∀ i (t : ℕ) (h : G.Hist t),
    P.historyPotential (lowerPotential i) t h ≤
      G.stageEUAt P.behaviorProfile h i + lowerCharge i t h
  upper_superharmonic : ∀ i (t : ℕ) (h : G.Hist t),
    G.historyContinuationEU P.behaviorProfile
        (P.historyPotential (upperPotential i)) h ≤
      P.historyPotential (upperPotential i) t h
  upper_stage : ∀ i (t : ℕ) (h : G.Hist t),
    G.stageEUAt P.behaviorProfile h i ≤
      P.historyPotential (upperPotential i) t h + upperCharge i t h
  deviation_superharmonic : ∀ i (dev : G.BehaviorStrategy i)
      (t : ℕ) (h : G.Hist t),
    G.historyContinuationEU (Function.update P.behaviorProfile i dev)
        (P.historyPotential (deviationPotential i)) h ≤
      P.historyPotential (deviationPotential i) t h
  deviation_stage : ∀ i (dev : G.BehaviorStrategy i)
      (t : ℕ) (h : G.Hist t),
    G.stageEUAt (Function.update P.behaviorProfile i dev) h i ≤
      P.historyPotential (deviationPotential i) t h + deviationCharge i dev t h
  lower_charge_cesaro : ∀ i T, horizon ≤ T →
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
      G.expectedHistoryValue P.behaviorProfile s₀ (lowerCharge i) t ≤ δ
  upper_charge_cesaro : ∀ i T, horizon ≤ T →
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
      G.expectedHistoryValue P.behaviorProfile s₀ (upperCharge i) t ≤ δ
  deviation_charge_cesaro : ∀ i (dev : G.BehaviorStrategy i) T, horizon ≤ T →
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
      G.expectedHistoryValue (Function.update P.behaviorProfile i dev) s₀
        (deviationCharge i dev) t ≤ δ

/-- A game has a public-phase punishment system when some public phase
profile carries the local certificate data. -/
def IsPublicPhasePunishmentSystemAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ) : Prop :=
  ∃ P : PublicPhaseProfile G, Nonempty (PublicPhasePunishmentSystemAt G P s₀ v δ)

/-- Compile historywise public-phase inequalities into the expectation-level
adaptive potential certificate. -/
theorem isAdaptivePotentialCertificateAt_of_isPublicPhasePunishmentSystemAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ)
    (hphase : G.IsPublicPhasePunishmentSystemAt s₀ v δ) :
    G.IsAdaptivePotentialCertificateAt s₀ v δ := by
  obtain ⟨P, ⟨C⟩⟩ := hphase
  let φlo : ι → G.HistoryPotential :=
    fun i => P.historyPotential (C.lowerPotential i)
  let φhi : ι → G.HistoryPotential :=
    fun i => P.historyPotential (C.upperPotential i)
  let φdv : ι → G.HistoryPotential :=
    fun i => P.historyPotential (C.deviationPotential i)
  let elo : ι → ℕ → ℝ :=
    fun i t => G.expectedHistoryValue P.behaviorProfile s₀ (C.lowerCharge i) t
  let ehi : ι → ℕ → ℝ :=
    fun i t => G.expectedHistoryValue P.behaviorProfile s₀ (C.upperCharge i) t
  let edv : ∀ i, G.BehaviorStrategy i → ℕ → ℝ :=
    fun i dev t => G.expectedHistoryValue
      (Function.update P.behaviorProfile i dev) s₀ (C.deviationCharge i dev) t
  refine ⟨P.behaviorProfile, C.horizon, φlo, φhi, φdv,
    elo, ehi, edv,
    C.horizon_ge_two, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact C.lower_initial
  · exact C.upper_initial
  · exact C.deviation_initial
  · intro i t
    rw [G.expectedHistoryValue_succ]
    unfold expectedHistoryValue
    exact expect_mono _ _ _ (C.lower_subharmonic i t)
  · intro i t
    unfold expectedHistoryValue expectedStagePayoff
    simpa only [φlo, elo, expectedHistoryValue, expect_add] using
      expect_mono (G.histDist P.behaviorProfile s₀ t) _ _
        (C.lower_stage i t)
  · intro i t
    rw [G.expectedHistoryValue_succ]
    unfold expectedHistoryValue
    exact expect_mono _ _ _ (C.upper_superharmonic i t)
  · intro i t
    unfold expectedHistoryValue expectedStagePayoff
    simpa only [φhi, ehi, expectedHistoryValue, expect_add] using
      expect_mono (G.histDist P.behaviorProfile s₀ t) _ _
        (C.upper_stage i t)
  · intro i dev t
    rw [G.expectedHistoryValue_succ]
    unfold expectedHistoryValue
    exact expect_mono _ _ _ (C.deviation_superharmonic i dev t)
  · intro i dev t
    unfold expectedHistoryValue expectedStagePayoff
    simpa only [φdv, edv, expectedHistoryValue, expect_add] using
      expect_mono
        (G.histDist (Function.update P.behaviorProfile i dev) s₀ t) _ _
        (C.deviation_stage i dev t)
  · exact C.lower_charge_cesaro
  · exact C.upper_charge_cesaro
  · exact C.deviation_charge_cesaro

end StochasticGame
end GameTheory
