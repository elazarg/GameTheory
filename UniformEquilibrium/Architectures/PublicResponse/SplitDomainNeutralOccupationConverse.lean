/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Architectures.PublicResponse.ResponseArchitectureMarkovDeviationLaw
import UniformEquilibrium.Architectures.PublicResponse.SplitDomainPrescribedBiasConverse
import Math.Probability.AnalyticOccupationRealization

/-!
# Split-domain neutral-occupation converse

The shifted unilateral cap at every node of an owner's closed arena already
forces the owner-local neutral-occupation condition (N).  The proof realizes
an arbitrary balanced occupation as a stationary configuration-Markov
deviation, averages the semantic cap over its invariant source law, and then
uses stationarity to identify every finite-horizon average with the occupation
reward.

The assumptions used by the realization are explicit:

* finite controller and action spaces;
* the cap at every node of the selected owner's arena, against every behavior
  deviation;
* pure-row support closure of that arena (the `SplitResponseDomain` field
  `unilateral_closed`).

No recurrent-coverage assumption and no separate realizability hypothesis is
used.  Zero-source-mass configurations receive the prescribed mixed action as
an arbitrary fallback; stationarity gives them zero weight.  In fact the proof
does not use target neutrality, so it establishes the stronger assertion for
every normalized balanced occupation supported in the owner arena.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability
open Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} {G : StochasticGame ι}

attribute [local instance] Fintype.ofFinite

namespace FiniteResponseArchitecture
namespace NeutralOccupationOn

variable {initial : G.State} {A : G.FiniteResponseArchitecture initial}
  [Fintype ι] [DecidableEq ι] [∀ i, Fintype (G.Act i)]
  {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι} {who : ι}

/-- Total occupation mass leaving one configuration. -/
def configMass (μ : A.NeutralOccupationOn R u who) (z : A.Config) : ℝ :=
  ∑ act : G.Act who, μ.mass (z, act)

theorem configMass_nonneg (μ : A.NeutralOccupationOn R u who)
    (z : A.Config) : 0 ≤ μ.configMass z := by
  exact Finset.sum_nonneg fun act _ => μ.mass_nonneg (z, act)

theorem sum_configMass (μ : A.NeutralOccupationOn R u who) :
    ∑ z : A.Config, μ.configMass z = 1 := by
  rw [show (∑ z : A.Config, μ.configMass z) =
      ∑ p : A.Config × G.Act who, μ.mass p by
    simp only [configMass, Fintype.sum_prod_type]]
  exact μ.total

/-- Positive outgoing mass can occur only at an owner-relevant source. -/
theorem relevant_of_configMass_pos (μ : A.NeutralOccupationOn R u who)
    {z : A.Config} (hz : 0 < μ.configMass z) : R.unilateral who z := by
  rw [configMass] at hz
  obtain ⟨act, -, hact⟩ := Finset.sum_pos_iff_of_nonneg
    (fun act _ => μ.mass_nonneg (z, act)) |>.mp hz
  exact μ.relevant_support (z, act) hact

/-- Invariant source law associated with the occupation. -/
def configInvariant (μ : A.NeutralOccupationOn R u who) : PMF A.Config :=
  finiteRealWeightsPMF μ.configMass μ.configMass_nonneg μ.sum_configMass

@[simp] theorem configInvariant_toReal
    (μ : A.NeutralOccupationOn R u who) (z : A.Config) :
    (μ.configInvariant z).toReal = μ.configMass z := by
  exact finiteRealWeightsPMF_toReal
    μ.configMass μ.configMass_nonneg μ.sum_configMass z

/-- Stationary mixed action obtained by disintegrating the occupation at each
positive-mass source.  The prescribed row is used only at zero-mass sources. -/
def configPolicy (μ : A.NeutralOccupationOn R u who)
    (z : A.Config) : PMF (G.Act who) := by
  classical
  exact if hz : 0 < μ.configMass z then
    finiteRealWeightsPMF
      (fun act => μ.mass (z, act) / μ.configMass z)
      (fun act => div_nonneg (μ.mass_nonneg (z, act)) hz.le)
      (by
        rw [← Finset.sum_div, configMass]
        exact div_self (ne_of_gt hz))
  else A.play z who

@[simp] theorem configPolicy_toReal_of_pos
    (μ : A.NeutralOccupationOn R u who) {z : A.Config}
    (hz : 0 < μ.configMass z) (act : G.Act who) :
    (μ.configPolicy z act).toReal = μ.mass (z, act) / μ.configMass z := by
  simp [configPolicy, hz,
    div_nonneg (μ.mass_nonneg (z, act)) hz.le]

theorem configMass_eq_zero_of_not_pos
    (μ : A.NeutralOccupationOn R u who) {z : A.Config}
    (hz : ¬ 0 < μ.configMass z) : μ.configMass z = 0 :=
  le_antisymm (not_lt.mp hz) (μ.configMass_nonneg z)

theorem mass_eq_zero_of_configMass_not_pos
    (μ : A.NeutralOccupationOn R u who) {z : A.Config}
    (hz : ¬ 0 < μ.configMass z) (act : G.Act who) :
    μ.mass (z, act) = 0 := by
  have hle : μ.mass (z, act) ≤ μ.configMass z := by
    rw [configMass]
    exact Finset.single_le_sum
      (s := Finset.univ)
      (fun other _ => μ.mass_nonneg (z, other))
      (Finset.mem_univ act)
  rw [μ.configMass_eq_zero_of_not_pos hz] at hle
  exact le_antisymm hle (μ.mass_nonneg (z, act))

/-- The realized policy stays in the declared owner arena from every relevant
source.  This is the only legal-realizability use of support closure. -/
theorem configPolicy_closed {z y : A.Config}
    (μ : A.NeutralOccupationOn R u who) (hz : R.unilateral who z)
    (hy : y ∈ (A.configMarkovKernel who μ.configPolicy z).support) :
    R.unilateral who y := by
  exact R.unilateral_closed_mixed who hz (μ.configPolicy z) hy

/-- At a positive-mass source, the induced configuration row is exactly the
occupation-weighted mixture of pure unilateral rows. -/
theorem configMarkovKernel_toReal_of_configMass_pos
    (μ : A.NeutralOccupationOn R u who) {z : A.Config}
    (hz : 0 < μ.configMass z) (y : A.Config) :
    (A.configMarkovKernel who μ.configPolicy z y).toReal =
      ∑ act : G.Act who,
        (μ.mass (z, act) / μ.configMass z) *
          (A.nextConfigDist who z (PMF.pure act) y).toReal := by
  unfold FiniteResponseArchitecture.configMarkovKernel
  rw [ClosedResponseRegion.nextConfigDist_eq_bind,
    Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
  apply Finset.sum_congr rfl
  intro act _
  rw [μ.configPolicy_toReal_of_pos hz act]

/-- At a positive-mass source, the induced stage reward is the corresponding
occupation-weighted mixture of pure-row rewards. -/
theorem configMarkovReward_of_configMass_pos
    (μ : A.NeutralOccupationOn R u who) {z : A.Config}
    (hz : 0 < μ.configMass z) :
    A.configMarkovReward who μ.configPolicy z =
      ∑ act : G.Act who,
        (μ.mass (z, act) / μ.configMass z) *
          A.stagePayoffAt who z (PMF.pure act) := by
  unfold FiniteResponseArchitecture.configMarkovReward
  rw [A.stagePayoffAt_eq_expect, expect_eq_sum]
  apply Finset.sum_congr rfl
  intro act _
  rw [μ.configPolicy_toReal_of_pos hz act]

/-- Ambient balance says that total occupation arrival at a configuration is
its outgoing source mass. -/
theorem sum_mass_transition_eq_configMass
    (μ : A.NeutralOccupationOn R u who) (y : A.Config) :
    (∑ z : A.Config, ∑ act : G.Act who,
      μ.mass (z, act) *
        (A.nextConfigDist who z (PMF.pure act) y).toReal) =
      μ.configMass y := by
  have hbalance := μ.balance y
  rw [Fintype.sum_prod_type] at hbalance
  simp only [mul_sub, Finset.sum_sub_distrib] at hbalance
  have hsource :
      (∑ z : A.Config, ∑ act : G.Act who,
        μ.mass (z, act) * (if y = z then 1 else 0)) =
        μ.configMass y := by
    rw [Fintype.sum_eq_single y]
    · simp [configMass]
    · intro z hzy
      simp [Ne.symm hzy]
  rw [hsource] at hbalance
  linarith

/-- The invariant source PMF is stationary under the realized ambient
configuration kernel. -/
theorem configInvariant_stationary_real
    (μ : A.NeutralOccupationOn R u who) (y : A.Config) :
    (∑ z : A.Config,
      (μ.configInvariant z).toReal *
        (A.configMarkovKernel who μ.configPolicy z y).toReal) =
      (μ.configInvariant y).toReal := by
  simp only [μ.configInvariant_toReal]
  calc
    (∑ z : A.Config,
        μ.configMass z *
          (A.configMarkovKernel who μ.configPolicy z y).toReal) =
        ∑ z : A.Config, ∑ act : G.Act who,
          μ.mass (z, act) *
            (A.nextConfigDist who z (PMF.pure act) y).toReal := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : 0 < μ.configMass z
      · rw [μ.configMarkovKernel_toReal_of_configMass_pos hz y,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro act _
        field_simp [ne_of_gt hz]
      · rw [μ.configMass_eq_zero_of_not_pos hz]
        simp [μ.mass_eq_zero_of_configMass_not_pos hz]
    _ = μ.configMass y := μ.sum_mass_transition_eq_configMass y

/-- PMF form of source-law stationarity. -/
theorem configInvariant_bind_configMarkovKernel
    (μ : A.NeutralOccupationOn R u who) :
    μ.configInvariant.bind
        (A.configMarkovKernel who μ.configPolicy) =
      μ.configInvariant := by
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro y
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
  exact μ.configInvariant_stationary_real y

/-- Invariant expected reward of the realized policy is the occupation's
mass-weighted pure-row reward. -/
theorem expect_configInvariant_configMarkovReward
    (μ : A.NeutralOccupationOn R u who) :
    expect μ.configInvariant
        (A.configMarkovReward who μ.configPolicy) =
      ∑ p : A.Config × G.Act who,
        μ.mass p * A.stagePayoffAt who p.1 (PMF.pure p.2) := by
  rw [expect_eq_sum, Fintype.sum_prod_type]
  simp only [μ.configInvariant_toReal]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : 0 < μ.configMass z
  · rw [μ.configMarkovReward_of_configMass_pos hz,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro act _
    field_simp [ne_of_gt hz]
  · rw [μ.configMass_eq_zero_of_not_pos hz]
    simp [μ.mass_eq_zero_of_configMass_not_pos hz]

/-- Invariant expected target is the occupation's mass-weighted source
target. -/
theorem expect_configInvariant_target
    (μ : A.NeutralOccupationOn R u who) :
    expect μ.configInvariant (fun z => u z who) =
      ∑ p : A.Config × G.Act who, μ.mass p * u p.1 who := by
  rw [expect_eq_sum, Fintype.sum_prod_type]
  simp only [μ.configInvariant_toReal, configMass]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_mul]

/-- The invariant source law remains invariant under every number of steps of
the realized configuration kernel. -/
theorem configInvariant_bind_configMarkovIter
    (μ : A.NeutralOccupationOn R u who) : ∀ t : ℕ,
    μ.configInvariant.bind
        (Math.PMFIter.iter
          (A.configMarkovKernel who μ.configPolicy) t) =
      μ.configInvariant := by
  intro t
  induction t with
  | zero =>
      rw [show Math.PMFIter.iter
          (A.configMarkovKernel who μ.configPolicy) 0 = PMF.pure by
        funext z
        rfl]
      exact PMF.bind_pure _
  | succ t ih =>
      rw [show Math.PMFIter.iter
          (A.configMarkovKernel who μ.configPolicy) (t + 1) =
          fun z =>
            (A.configMarkovKernel who μ.configPolicy z).bind
              (Math.PMFIter.iter
                (A.configMarkovKernel who μ.configPolicy) t) by
        funext z
        exact Math.PMFIter.iter_succ _ z t]
      rw [← PMF.bind_bind,
        μ.configInvariant_bind_configMarkovKernel, ih]

/-- Pure-row closure makes every supported configuration of the realized
stationary policy remain in the owner arena. -/
theorem configMarkovIter_relevant
    (μ : A.NeutralOccupationOn R u who) {z : A.Config}
    (hz : R.unilateral who z) : ∀ (t : ℕ) (y : A.Config),
    y ∈ (Math.PMFIter.iter
      (A.configMarkovKernel who μ.configPolicy) t z).support →
      R.unilateral who y := by
  intro t
  induction t generalizing z with
  | zero =>
      intro y hy
      have hyz : y = z := by simpa using hy
      subst y
      exact hz
  | succ t ih =>
      intro y hy
      rw [Math.PMFIter.iter_succ, PMF.mem_support_bind_iff] at hy
      obtain ⟨next, hnext, hy⟩ := hy
      exact ih (μ.configPolicy_closed hz hnext) y hy

/-- Full public-history form of legal realization: starting from any relevant
configuration, every supported history under the stationary occupation policy
projects to a configuration in the declared owner arena. -/
theorem configAt_rebase_configPolicy_relevant_of_mem_support
    (μ : A.NeutralOccupationOn R u who) {z : A.Config}
    (hz : R.unilateral who z) {t : ℕ} (h : G.Hist t)
    (hh : h ∈ (G.histDist
      ((A.rebase z).configMarkovProfile who μ.configPolicy)
      (A.publicState z) t).support) :
    R.unilateral who ((A.rebase z).configAt t h) := by
  have hmapped : (A.rebase z).configAt t h ∈
      ((G.histDist
        ((A.rebase z).configMarkovProfile who μ.configPolicy)
        (A.publicState z) t).map
          ((A.rebase z).configAt t)).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨h, hh, rfl⟩
  rw [(A.rebase z).map_configAt_histDist_configMarkovProfile
    who μ.configPolicy t] at hmapped
  exact μ.configMarkovIter_relevant hz t _ hmapped

/-- Every iterated reward has the same expectation under the invariant source
law. -/
theorem expect_configInvariant_iter_configMarkovReward
    (μ : A.NeutralOccupationOn R u who) (t : ℕ) :
    expect μ.configInvariant (fun z =>
        expect
          (Math.PMFIter.iter
            (A.configMarkovKernel who μ.configPolicy) t z)
          (A.configMarkovReward who μ.configPolicy)) =
      expect μ.configInvariant
        (A.configMarkovReward who μ.configPolicy) := by
  rw [← expect_bind, μ.configInvariant_bind_configMarkovIter t]

/-- The invariant expectation of the unnormalized `T`-stage reward sum is
`T` times the invariant one-stage reward. -/
theorem expect_configInvariant_sum_iter_configMarkovReward
    (μ : A.NeutralOccupationOn R u who) : ∀ T : ℕ,
    expect μ.configInvariant (fun z =>
        ∑ t ∈ Finset.range T,
          expect
            (Math.PMFIter.iter
              (A.configMarkovKernel who μ.configPolicy) t z)
            (A.configMarkovReward who μ.configPolicy)) =
      (T : ℝ) * expect μ.configInvariant
        (A.configMarkovReward who μ.configPolicy) := by
  intro T
  induction T with
  | zero => simp [expect_const]
  | succ T ih =>
      rw [show (fun z =>
          ∑ t ∈ Finset.range (T + 1),
            expect
              (Math.PMFIter.iter
                (A.configMarkovKernel who μ.configPolicy) t z)
              (A.configMarkovReward who μ.configPolicy)) =
          fun z =>
            (∑ t ∈ Finset.range T,
              expect
                (Math.PMFIter.iter
                  (A.configMarkovKernel who μ.configPolicy) t z)
                (A.configMarkovReward who μ.configPolicy)) +
            expect
              (Math.PMFIter.iter
                (A.configMarkovKernel who μ.configPolicy) T z)
              (A.configMarkovReward who μ.configPolicy) by
        funext z
        rw [Finset.sum_range_succ]]
      rw [expect_add, ih,
        μ.expect_configInvariant_iter_configMarkovReward T]
      push_cast
      ring

/-- Every positive-horizon configuration Cesaro payoff has exactly the
one-stage invariant occupation reward when averaged under the invariant
source law. -/
theorem expect_configInvariant_configMarkovCesaroPayoff
    (μ : A.NeutralOccupationOn R u who) {T : ℕ} (hT : 0 < T) :
    expect μ.configInvariant
        (fun z => A.configMarkovCesaroPayoff who μ.configPolicy z T) =
      expect μ.configInvariant
        (A.configMarkovReward who μ.configPolicy) := by
  unfold FiniteResponseArchitecture.configMarkovCesaroPayoff
  calc
    expect μ.configInvariant (fun z =>
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
          expect
            (Math.PMFIter.iter
              (A.configMarkovKernel who μ.configPolicy) t z)
            (A.configMarkovReward who μ.configPolicy)) =
        (T : ℝ)⁻¹ * expect μ.configInvariant (fun z =>
          ∑ t ∈ Finset.range T,
            expect
              (Math.PMFIter.iter
                (A.configMarkovKernel who μ.configPolicy) t z)
              (A.configMarkovReward who μ.configPolicy)) := by
      exact expect_const_mul _ _ _
    _ = (T : ℝ)⁻¹ * ((T : ℝ) *
          expect μ.configInvariant
            (A.configMarkovReward who μ.configPolicy)) := by
      rw [μ.expect_configInvariant_sum_iter_configMarkovReward T]
    _ = expect μ.configInvariant
          (A.configMarkovReward who μ.configPolicy) := by
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hT)]

variable [Finite G.State]

/-- Shifted semantic caps on every source in a closed owner arena force the
surplus of every normalized balanced occupation supported there to be
nonpositive.

Target-neutrality is not used: the conclusion holds for the larger class of
all balanced occupations carried by the arena. -/
theorem surplus_nonpos_of_history_unilateralCap
    (μ : A.NeutralOccupationOn R u who)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hcap : ∀ (z : A.Config), R.unilateral who z →
      ∀ dev : G.BehaviorStrategy who, ∀ᶠ T : ℕ in atTop,
        G.finiteAveragePayoff (A.publicState z) T
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          who ≤ u z who + error T) :
    μ.surplus ≤ 0 := by
  have hconfigCap : ∀ᶠ T : ℕ in atTop,
      ∀ z : A.Config, R.unilateral who z →
        A.configMarkovCesaroPayoff who μ.configPolicy z T ≤
          u z who + error T := by
    apply Filter.eventually_all.mpr
    intro z
    by_cases hz : R.unilateral who z
    · filter_upwards
        [hcap z hz
          ((A.rebase z).configMarkovDeviation who μ.configPolicy)]
        with T hT
      intro _
      rw [show Function.update
          (A.rebase z).phaseProfile.behaviorProfile who
            ((A.rebase z).configMarkovDeviation who μ.configPolicy) =
          (A.rebase z).configMarkovProfile who μ.configPolicy by rfl,
        A.finiteAveragePayoff_configMarkovProfile_rebase_eq_configCesaro
          z who μ.configPolicy T] at hT
      exact hT
    · exact Filter.Eventually.of_forall fun _ hrel => (hz hrel).elim
  have hinvariantCap : ∀ᶠ T : ℕ in atTop,
      expect μ.configInvariant
          (A.configMarkovReward who μ.configPolicy) ≤
        expect μ.configInvariant (fun z => u z who) + error T := by
    filter_upwards [hconfigCap, eventually_ge_atTop (1 : ℕ)]
      with T hT hTpos
    calc
      expect μ.configInvariant
          (A.configMarkovReward who μ.configPolicy) =
          expect μ.configInvariant (fun z =>
            A.configMarkovCesaroPayoff who μ.configPolicy z T) :=
        (μ.expect_configInvariant_configMarkovCesaroPayoff hTpos).symm
      _ ≤ expect μ.configInvariant (fun z => u z who + error T) := by
        rw [expect_eq_sum, expect_eq_sum]
        apply Finset.sum_le_sum
        intro z _
        rw [μ.configInvariant_toReal]
        by_cases hz : 0 < μ.configMass z
        · exact mul_le_mul_of_nonneg_left
            (hT z (μ.relevant_of_configMass_pos hz))
            (μ.configMass_nonneg z)
        · rw [μ.configMass_eq_zero_of_not_pos hz]
          simp
      _ = expect μ.configInvariant (fun z => u z who) + error T := by
        rw [expect_add, expect_const]
  have hrewardTarget :
      expect μ.configInvariant
          (A.configMarkovReward who μ.configPolicy) ≤
        expect μ.configInvariant (fun z => u z who) := by
    have hlimit := le_of_tendsto_of_tendsto tendsto_const_nhds
      ((tendsto_const_nhds : Tendsto
        (fun _ : ℕ => expect μ.configInvariant (fun z => u z who))
        atTop (nhds (expect μ.configInvariant (fun z => u z who)))).add herror)
      hinvariantCap
    simpa using hlimit
  calc
    μ.surplus =
        (∑ p : A.Config × G.Act who,
          μ.mass p * A.stagePayoffAt who p.1 (PMF.pure p.2)) -
        ∑ p : A.Config × G.Act who, μ.mass p * u p.1 who := by
      simp only [surplus, mul_sub, Finset.sum_sub_distrib]
    _ = expect μ.configInvariant
          (A.configMarkovReward who μ.configPolicy) -
        expect μ.configInvariant (fun z => u z who) := by
      rw [μ.expect_configInvariant_configMarkovReward,
        μ.expect_configInvariant_target]
    _ ≤ 0 := sub_nonpos.mpr hrewardTarget

end NeutralOccupationOn

namespace ClosedResponseRegion

variable {initial : G.State} {A : G.FiniteResponseArchitecture initial}
  [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- All-start semantic unilateral caps imply owner-local (N) on any closed
response region. -/
theorem neutralOccupationNonpositive_of_history_unilateralCap
    (R : A.ClosedResponseRegion) (u : A.Config → Payoff ι)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hcap : ∀ (who : ι) (z : A.Config), R.unilateral who z →
      ∀ dev : G.BehaviorStrategy who, ∀ᶠ T : ℕ in atTop,
        G.finiteAveragePayoff (A.publicState z) T
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          who ≤ u z who + error T) :
    A.IsNeutralOccupationNonpositiveOn R u := by
  intro who μ
  exact μ.surplus_nonpos_of_history_unilateralCap error herror
    (hcap who)

end ClosedResponseRegion

namespace SplitResponseDomain

variable {initial : G.State} {A : G.FiniteResponseArchitecture initial}
  [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- Exact split-domain form: caps at every node of each owner arena imply the
owner-local neutral-occupation packet (N), without recurrent coverage or an
extra occupation-realizability axiom. -/
theorem neutralOccupationNonpositive_of_history_unilateralCap
    (D : A.SplitResponseDomain) (u : A.Config → Payoff ι)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hcap : ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ dev : G.BehaviorStrategy who, ∀ᶠ T : ℕ in atTop,
        G.finiteAveragePayoff (A.publicState z) T
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          who ≤ u z who + error T) :
    A.IsNeutralOccupationNonpositiveOn D.ownerRegion u :=
  D.ownerRegion.neutralOccupationNonpositive_of_history_unilateralCap
    u error herror hcap

/-- **Semantic necessity-to-verifier capstone.** Shifted prescribed
delivery and shifted unilateral caps now synthesize both gain--bias families
on their exact split domains; (N) is derived rather than assumed. -/
theorem exists_gainBiases_of_historyDelivery_and_unilateralCap
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hdelivery : ∀ (who : ι) (z : A.Config), D.delivery z →
      Tendsto (fun T : ℕ =>
        G.finiteAveragePayoff (A.publicState z) T
          (A.rebase z).phaseProfile.behaviorProfile who)
        atTop (nhds (u z who)))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (hcap : ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ dev : G.BehaviorStrategy who, ∀ᶠ T : ℕ in atTop,
        G.finiteAveragePayoff (A.publicState z) T
          (Function.update (A.rebase z).phaseProfile.behaviorProfile who dev)
          who ≤ u z who + error T) :
    ∃ prescribedBias unilateralBias : ι → A.Config → ℝ,
      (∀ (who : ι) (z : A.Config), D.delivery z →
        u z who + prescribedBias who z = A.prescribedStagePayoff z who +
          expect (A.prescribedConfigDist z) (prescribedBias who)) ∧
      (∀ (who : ι) (z : A.Config), D.unilateral who z →
        ∀ act : G.Act who,
          A.stagePayoffAt who z (PMF.pure act) +
              expect (A.nextConfigDist who z (PMF.pure act))
                (unilateralBias who) ≤
            u z who + unilateralBias who z) := by
  exact D.exists_gainBiases_of_historyDelivery_cap_and_neutralOccupation
    hdelivery error herror hcap
    (D.neutralOccupationNonpositive_of_history_unilateralCap
      u error herror hcap)

end SplitResponseDomain
end FiniteResponseArchitecture
end StochasticGame
end GameTheory
