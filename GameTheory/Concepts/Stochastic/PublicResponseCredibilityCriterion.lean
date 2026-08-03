/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AdaptiveSystemEnforcementLedger
import Math.Probability.ChargedOccupationAlternative

/-!
# The finite credibility criterion for a public response architecture

This file supplies the *criterion direction* of the finite credibility
theorem: from the four named finite conditions on a fixed finite closed
response architecture to the operational
`StochasticGame.PublicResponseEnforcementLedgerAt` that the existing
compilers consume.

The tree already contained the *consumer* direction and the negative
boundary.  It could consume an enforcement ledger
(`PublicResponseEnforcementCompiler`, `AdaptiveSystemEnforcementLedger`,
`ProcessedHarmonicPublicResponseEnforcement`) and it could refute one on the
detector example (`PublicResponseCredibilityBoundary`).  Nothing *produced*
one from finite configuration data.  Neither of those is the converse of
"(T0), (Ti), (N), (P) ⟹ ledger": a genuine converse would recover the
occupation conditions from configuration-based ledger data, and is not
proved here.

## The architecture

`FiniteResponseArchitecture` is the finite closed response architecture: a
finite public configuration set with an initial configuration, a public
state projection, a prescribed mixed row at every configuration, and a
*total* public update rule defined after every joint action and every next
state — in particular after every history reachable under a unilateral
deviation.  Response, reserve, reset and child-entry modes are configurations
like any other, *provided the child continuation is itself internalized in
this finite controller*.  A child whose continuation is history dependent, or
supplied recursively by a separate certificate, is not covered: it needs a
handoff adapter that first compiles the child into finitely many
configurations of this controller.

## The four conditions

For a complete target assignment `u : Config → Payoff ι`:

* `IsPrescribedTargetHarmonic` — (T0), `P⁰ uᵢ = uᵢ`;
* `IsUnilateralTargetSuperharmonic` — (Ti), `Pᵢ^{aᵢ} uᵢ ≤ uᵢ`;
* `IsNeutralOccupationNonpositive` — (N), every normalized invariant
  occupation supported on target-neutral pairs has nonpositive actual
  payoff surplus;
* `IsPrescribedDelivery` — (P), every stationary distribution of the
  prescribed kernel delivers at least the target.

None of the four mentions a ledger, a potential, a punishment system or a
deviation-payoff cap.  The bounded potentials and the `O(1)` target-charge
residual are *produced* by finite Farkas duality
(`Math.Probability.normalizedPositiveChargedCirculation_xor_driftPotential`),
exactly as in the answer.

The bundle is called `IsGlobalCredibilityCriterion`: see "Scope" below.

## Main results

* `FiniteResponseArchitecture.exists_deviationPotential` — (Ti) and (N)
  give a bounded configuration potential absorbing every unilateral row;
  this is the Farkas step (16)–(19), including the finite constant `Cᵢ`.
* `FiniteResponseArchitecture.exists_deliveryPotential` — (P) gives the
  prescribed-play potential (21).
* `FiniteResponseArchitecture.exists_uniformModulus_of_isGlobalCredibilityCriterion`
  — the quantitative form: one explicit modulus `M` with prescribed
  delivery within `M / T` and every unilateral deviation capped by
  `u(z₀) + M / T`, uniformly in the horizon and in the deviation.
* `FiniteResponseArchitecture.nonempty_publicResponseEnforcementLedgerAt` —
  the criterion direction proper: the four conditions give the in-tree
  `PublicResponseEnforcementLedgerAt` at every positive error.
* `FiniteResponseArchitecture.nonempty_publicResponseEnforcementLedgerAt_rebase`
  — the handoff payoff of the global hypotheses: the same architecture
  restarted at *any* configuration `z` delivers the ledger for the target
  `u z`, so a response system may hand control over at any configuration.

The deviation stage gap is booked as the ledger's `continuationResidual`,
not its `monitoringResidual`: the cap comes from the strategic conditions
(Ti) and (N) through the continuation potential, and no detector, alarm or
statistical estimate participates.  The ledger's monitoring account is
identically zero here.

## Falsifier fences

`CredibilityCriterionProbe` checks the conditions against the in-tree
boundary example (`ActionDetectorNoAutomaticCloser.game`, whose feasible
target admits no ledger at all).  The criterion rejects it, and rejects it
for exactly the right reason: (T0), (Ti) and (P) all hold there and (N)
fails.  Each of the four conditions is separately refutable and the whole
bundle is satisfiable, so no condition is vacuous.

## Scope

Conditions (T0), (Ti), (N), (P) are quantified over *all* configurations of
the supplied architecture.  The answer quantifies (Ti) and (N) over the
configurations reachable under a unilateral behavior of the owner, and (P)
over prescribed-reachable recurrent classes.  The two readings agree on an
architecture supplied already pruned to its relevant configurations, which
is the convention of the answer's §1 ("Only configurations reachable under
some unilateral behavior of `i` … are relevant for player `i`").  On an
unpruned architecture the conditions here are strictly stronger, so the
implication proved below remains valid but is not tight.  The companion module
`ReachablePublicResponseCredibilityCriterion` supplies a support-pruned
formulation at a declared entry, its canonical least reachable region, and
the same ledger and adaptive-certificate consumers.  It is still a sound
criterion direction.  The stronger converse for uniform statements based at
every state in the union of owner-specific arenas needs the recurrent-class
coverage/fifth-obstruction correction of Question 96.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct

variable {ι : Type} {G : StochasticGame ι}

-- ---------------------------------------------------------------------------
-- Generic telescopes, Cesàro identities and history comparisons
-- ---------------------------------------------------------------------------

/-- One-step supermartingale telescope for real sequences. -/
theorem sumStep_telescope_le {P U W : ℕ → ℝ}
    (hstep : ∀ t, P t + W (t + 1) ≤ U t + W t) (T : ℕ) :
    (∑ t ∈ Finset.range T, P t) + W T ≤
      (∑ t ∈ Finset.range T, U t) + W 0 := by
  induction T with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hn := hstep n
      linarith

/-- One-step submartingale telescope for real sequences. -/
theorem sumStep_telescope_ge {P U W : ℕ → ℝ}
    (hstep : ∀ t, U t + W t ≤ P t + W (t + 1)) (T : ℕ) :
    (∑ t ∈ Finset.range T, U t) + W 0 ≤
      (∑ t ∈ Finset.range T, P t) + W T := by
  induction T with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hn := hstep n
      linarith

/-- Cesàro average of the realized stage gap above a constant. -/
theorem inv_mul_sum_expectedHistoryValue_stageEUAt_sub
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) (c : ℝ) {T : ℕ}
    (hT : 0 < T) :
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        G.expectedHistoryValue σ s₀
          (fun _ h => G.stageEUAt σ h who - c) t =
      G.finiteAveragePayoff s₀ T σ who - c := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp only [expectedHistoryValue, expectedStagePayoff, expect_sub,
    expect_const, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hT)]

/-- Cesàro average of the realized stage gap below a constant. -/
theorem inv_mul_sum_expectedHistoryValue_sub_stageEUAt
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) (c : ℝ) {T : ℕ}
    (hT : 0 < T) :
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        G.expectedHistoryValue σ s₀
          (fun _ h => c - G.stageEUAt σ h who) t =
      c - G.finiteAveragePayoff s₀ T σ who := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp only [expectedHistoryValue, expectedStagePayoff, expect_sub,
    expect_const, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hT)]

/-- A pointwise comparison at the initial history and at every later history
suffices to compare expectations along the realized law.  Histories of
positive length carry their own current state, so the only history whose
public bookkeeping has to be checked separately is the initial one. -/
theorem expect_histDist_le_of_succ
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State)
    (f g : (t : ℕ) → G.Hist t → ℝ)
    (hzero : f 0 (G.emptyHist s₀) ≤ g 0 (G.emptyHist s₀))
    (hsucc : ∀ (t : ℕ) (h : G.Hist (t + 1)), f (t + 1) h ≤ g (t + 1) h)
    (t : ℕ) :
    expect (G.histDist σ s₀ t) (f t) ≤ expect (G.histDist σ s₀ t) (g t) := by
  cases t with
  | zero => rw [G.histDist_zero]; simpa using hzero
  | succ n => exact expect_mono _ _ _ (hsucc n)

/-- Equality version of `expect_histDist_le_of_succ`. -/
theorem expect_histDist_congr_of_succ
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State)
    (f g : (t : ℕ) → G.Hist t → ℝ)
    (hzero : f 0 (G.emptyHist s₀) = g 0 (G.emptyHist s₀))
    (hsucc : ∀ (t : ℕ) (h : G.Hist (t + 1)), f (t + 1) h = g (t + 1) h)
    (t : ℕ) :
    expect (G.histDist σ s₀ t) (f t) = expect (G.histDist σ s₀ t) (g t) := by
  cases t with
  | zero => rw [G.histDist_zero]; simpa using hzero
  | succ n => exact congrArg _ (funext (hsucc n))

-- ---------------------------------------------------------------------------
-- The finite closed response architecture
-- ---------------------------------------------------------------------------

/-- A **finite closed response architecture** (Question 56, §1).

`Config` collects the normal, monitoring, response, reserve, reset and
child-entry modes into one finite public configuration set; `publicState`
is the projection `s : Z → S`; `play` is the prescribed mixed profile `x_z`;
and `step` is the *total* public update rule `F(z, a, s')`, defined for
every joint action and every next state, hence after every history reachable
under a unilateral deviation. -/
structure FiniteResponseArchitecture (G : StochasticGame ι)
    (initial : G.State) where
  /-- Finite public configuration set `Z`. -/
  Config : Type
  [configFintype : Fintype Config]
  [configDecidableEq : DecidableEq Config]
  /-- Initial configuration `z₀`. -/
  start : Config
  /-- Public state projection `s : Z → S`. -/
  publicState : Config → G.State
  /-- Prescribed mixed action profile `x_z`. -/
  play : Config → ∀ i, PMF (G.Act i)
  /-- Total public update rule `F(z, a, s')`. -/
  step : Config → G.JointAct → G.State → Config
  start_publicState : publicState start = initial
  step_publicState : ∀ z a s', publicState (step z a s') = s'

attribute [instance] FiniteResponseArchitecture.configFintype
attribute [instance] FiniteResponseArchitecture.configDecidableEq

namespace FiniteResponseArchitecture

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)

/-- Restart a closed architecture at one of its configurations.

The controller, prescribed play, and total public update are unchanged; only
the initial configuration and therefore the initial public state change. -/
abbrev rebase (z : A.Config) :
    G.FiniteResponseArchitecture (A.publicState z) where
  Config := A.Config
  configFintype := A.configFintype
  configDecidableEq := A.configDecidableEq
  start := z
  publicState := A.publicState
  play := A.play
  step := A.step
  start_publicState := rfl
  step_publicState := A.step_publicState

@[simp] theorem rebase_start (z : A.Config) : (A.rebase z).start = z := rfl

@[simp] theorem rebase_publicState (z y : A.Config) :
    (A.rebase z).publicState y = A.publicState y := rfl

@[simp] theorem rebase_play (z y : A.Config) :
    (A.rebase z).play y = A.play y := rfl

@[simp] theorem rebase_step (z y : A.Config) (act : G.JointAct)
    (s' : G.State) :
    (A.rebase z).step y act s' = A.step y act s' := rfl

-- ---------------------------------------------------------------------------
-- Configuration-level kernels and payoffs
-- ---------------------------------------------------------------------------

section BasicControllerRows

variable [Fintype ι] [DecidableEq ι]

/-- Joint action law at `z` when `who` plays `mixed` unilaterally. -/
def actionDist (who : ι) (z : A.Config) (mixed : PMF (G.Act who)) :
    PMF G.JointAct :=
  pmfPi (Function.update (A.play z) who mixed)

/-- Prescribed joint action law at `z`. -/
def prescribedActionDist (z : A.Config) : PMF G.JointAct :=
  pmfPi (A.play z)

theorem prescribedActionDist_eq (who : ι) (z : A.Config) :
    A.prescribedActionDist z = A.actionDist who z (A.play z who) := by
  simp [prescribedActionDist, actionDist]

/-- Mixing identity: a mixed unilateral row is the corresponding mixture of
pure unilateral rows. -/
theorem actionDist_eq_bind (who : ι) (z : A.Config)
    (mixed : PMF (G.Act who)) :
    A.actionDist who z mixed =
      mixed.bind fun act => A.actionDist who z (PMF.pure act) :=
  Math.PMFProduct.pmfPi_update_bind (A.play z) who mixed

end BasicControllerRows

section PayoffRows

variable [Fintype ι] [DecidableEq ι]

/-- The expected stage payoff `g_i^{a_i}(z)` of a unilateral row. -/
def stagePayoffAt (who : ι) (z : A.Config) (mixed : PMF (G.Act who)) : ℝ :=
  expect (A.actionDist who z mixed) fun act =>
    G.stagePayoff (A.publicState z) act who

/-- The prescribed expected stage payoff `g_i^0(z)`. -/
def prescribedStagePayoff (z : A.Config) (who : ι) : ℝ :=
  expect (A.prescribedActionDist z) fun act =>
    G.stagePayoff (A.publicState z) act who

end PayoffRows

section BasicPayoffIdentity

variable [Fintype ι] [DecidableEq ι]

theorem prescribedStagePayoff_eq (who : ι) (z : A.Config) :
    A.prescribedStagePayoff z who = A.stagePayoffAt who z (A.play z who) := by
  simp [prescribedStagePayoff, stagePayoffAt, A.prescribedActionDist_eq who z]

end BasicPayoffIdentity

section PayoffRows

variable [Fintype ι] [DecidableEq ι] [∀ i, Finite (G.Act i)]

theorem stagePayoffAt_eq_expect (who : ι) (z : A.Config)
    (mixed : PMF (G.Act who)) :
    A.stagePayoffAt who z mixed =
      expect mixed fun act => A.stagePayoffAt who z (PMF.pure act) := by
  unfold stagePayoffAt
  rw [A.actionDist_eq_bind who z mixed, expect_bind]

end PayoffRows

section BasicControllerKernels

variable [Fintype ι] [DecidableEq ι]

/-- The induced configuration kernel `P_i^{a_i}(z, ·)` of formula (5). -/
def nextConfigDist (who : ι) (z : A.Config) (mixed : PMF (G.Act who)) :
    PMF A.Config :=
  (A.actionDist who z mixed).bind fun act =>
    (G.transition (A.publicState z) act).bind fun s' =>
      PMF.pure (A.step z act s')

/-- The prescribed configuration kernel `P⁰(z, ·)`. -/
def prescribedConfigDist (z : A.Config) : PMF A.Config :=
  (A.prescribedActionDist z).bind fun act =>
    (G.transition (A.publicState z) act).bind fun s' =>
      PMF.pure (A.step z act s')

theorem prescribedConfigDist_eq (who : ι) (z : A.Config) :
    A.prescribedConfigDist z = A.nextConfigDist who z (A.play z who) := by
  simp [prescribedConfigDist, nextConfigDist, A.prescribedActionDist_eq who z]

theorem expect_nextConfigDist (who : ι) (z : A.Config)
    (mixed : PMF (G.Act who)) (f : A.Config → ℝ) :
    expect (A.nextConfigDist who z mixed) f =
      expect (A.actionDist who z mixed) fun act =>
        expect (G.transition (A.publicState z) act) fun s' =>
          f (A.step z act s') := by
  simp only [nextConfigDist, expect_bind, expect_pure]

end BasicControllerKernels

section PrescribedKernelExpectation

variable [Fintype ι]

theorem expect_prescribedConfigDist (z : A.Config) (f : A.Config → ℝ) :
    expect (A.prescribedConfigDist z) f =
      expect (A.prescribedActionDist z) fun act =>
        expect (G.transition (A.publicState z) act) fun s' =>
          f (A.step z act s') := by
  simp only [prescribedConfigDist, expect_bind, expect_pure]

end PrescribedKernelExpectation

section MixedRows

variable [Fintype ι] [DecidableEq ι] [∀ i, Finite (G.Act i)]

theorem expect_nextConfigDist_eq_expect (who : ι) (z : A.Config)
    (mixed : PMF (G.Act who)) (f : A.Config → ℝ) :
    expect (A.nextConfigDist who z mixed) f =
      expect mixed fun act =>
        expect (A.nextConfigDist who z (PMF.pure act)) f := by
  rw [A.expect_nextConfigDist who z mixed f, A.actionDist_eq_bind who z mixed,
    expect_bind]
  exact congrArg _ (funext fun act =>
    (A.expect_nextConfigDist who z (PMF.pure act) f).symm)

end MixedRows

section BasicRebaseAndTargets

variable [Fintype ι] [DecidableEq ι]

@[simp] theorem rebase_actionDist_eq (start : A.Config) (who : ι)
    (z : A.Config) (mixed : PMF (G.Act who)) :
    (A.rebase start).actionDist who z mixed = A.actionDist who z mixed := rfl

end BasicRebaseAndTargets

section PrescribedRebaseIdentity

variable [Fintype ι]

@[simp] theorem rebase_prescribedActionDist_eq (start z : A.Config) :
    (A.rebase start).prescribedActionDist z = A.prescribedActionDist z := rfl

end PrescribedRebaseIdentity

section BasicRebaseAndTargets

variable [Fintype ι] [DecidableEq ι]

@[simp] theorem rebase_stagePayoffAt_eq (start : A.Config) (who : ι)
    (z : A.Config) (mixed : PMF (G.Act who)) :
    (A.rebase start).stagePayoffAt who z mixed =
      A.stagePayoffAt who z mixed := rfl

end BasicRebaseAndTargets

section PrescribedRebaseIdentity

variable [Fintype ι]

@[simp] theorem rebase_prescribedStagePayoff_eq (start z : A.Config)
    (who : ι) :
    (A.rebase start).prescribedStagePayoff z who =
      A.prescribedStagePayoff z who := rfl

end PrescribedRebaseIdentity

section BasicRebaseAndTargets

variable [Fintype ι] [DecidableEq ι]

@[simp] theorem rebase_nextConfigDist_eq (start : A.Config) (who : ι)
    (z : A.Config) (mixed : PMF (G.Act who)) :
    (A.rebase start).nextConfigDist who z mixed =
      A.nextConfigDist who z mixed := rfl

end BasicRebaseAndTargets

section PrescribedRebaseIdentity

variable [Fintype ι]

@[simp] theorem rebase_prescribedConfigDist_eq (start z : A.Config) :
    (A.rebase start).prescribedConfigDist z =
      A.prescribedConfigDist z := rfl

end PrescribedRebaseIdentity

section BasicRebaseAndTargets

variable [Fintype ι] [DecidableEq ι]

-- ---------------------------------------------------------------------------
-- The four conditions
-- ---------------------------------------------------------------------------

/-- The target charge `d_i(z, a_i) = u_i(z) - P_i^{a_i} u_i(z)` of (8). -/
def targetCharge (u : A.Config → Payoff ι) (who : ι) (z : A.Config)
    (act : G.Act who) : ℝ :=
  u z who - expect (A.nextConfigDist who z (PMF.pure act)) fun y => u y who

@[simp] theorem rebase_targetCharge_eq (start : A.Config)
    (u : A.Config → Payoff ι) (who : ι) (z : A.Config)
    (act : G.Act who) :
    (A.rebase start).targetCharge u who z act =
      A.targetCharge u who z act := by
  simp [targetCharge]

/-- **(T0)** `P⁰ u_i = u_i`: the target is harmonic for the prescribed
kernel. -/
def IsPrescribedTargetHarmonic (u : A.Config → Payoff ι) : Prop :=
  ∀ (who : ι) (z : A.Config),
    expect (A.prescribedConfigDist z) (fun y => u y who) = u z who

/-- **(Ti)** `P_i^{a_i} u_i ≤ u_i`: the target is superharmonic for every
unilateral row of every player. -/
def IsUnilateralTargetSuperharmonic (u : A.Config → Payoff ι) : Prop :=
  ∀ (who : ι) (z : A.Config) (act : G.Act who),
    expect (A.nextConfigDist who z (PMF.pure act)) (fun y => u y who) ≤
      u z who

end BasicRebaseAndTargets

section FiniteUnilateralOccupations

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (G.Act i)]

/-- A normalized invariant occupation carried by target-neutral pairs: the
polytope `Ω_i^0(u)` of (9), in the standard occupation-column form used
elsewhere in the tree (arrival mass minus the unit of mass consumed at the
source). -/
structure NeutralOccupation (u : A.Config → Payoff ι) (who : ι) where
  /-- Occupation mass on configuration/own-action pairs. -/
  mass : A.Config × G.Act who → ℝ
  mass_nonneg : ∀ p, 0 ≤ mass p
  /-- `μ(z, a_i) > 0 ⟹ d_i(z, a_i) = 0`. -/
  neutral_support : ∀ p, 0 < mass p → A.targetCharge u who p.1 p.2 = 0
  /-- Invariance of the occupation under the owner's own kernel. -/
  balance : ∀ y : A.Config,
    ∑ p : A.Config × G.Act who,
      mass p * ((A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal -
        if y = p.1 then 1 else 0) = 0
  total : ∑ p : A.Config × G.Act who, mass p = 1

namespace NeutralOccupation

variable {A} {u : A.Config → Payoff ι} {who : ι}

/-- The actual payoff surplus `∑ μ(z,a)(g_i^{a}(z) - u_i(z))` of (N). -/
def surplus (μ : A.NeutralOccupation u who) : ℝ :=
  ∑ p : A.Config × G.Act who,
    μ.mass p * (A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who)

/-- The occupation-column balance in the flow form of (9): the mass leaving
a configuration equals the mass arriving there. -/
theorem balance_flow (μ : A.NeutralOccupation u who) (y : A.Config) :
    ∑ act : G.Act who, μ.mass (y, act) =
      ∑ p : A.Config × G.Act who,
        μ.mass p * (A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal := by
  have hb := μ.balance y
  have hsplit :
      ∑ p : A.Config × G.Act who,
          μ.mass p * ((A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal -
            if y = p.1 then 1 else 0) =
        (∑ p : A.Config × G.Act who,
            μ.mass p * (A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal) -
          ∑ p : A.Config × G.Act who,
            μ.mass p * (if y = p.1 then 1 else 0) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hdelta :
      ∑ p : A.Config × G.Act who,
          μ.mass p * (if y = p.1 then 1 else 0) =
        ∑ act : G.Act who, μ.mass (y, act) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun z _ =>
      show ∑ act : G.Act who, μ.mass (z, act) * (if y = z then 1 else 0) =
          if y = z then ∑ act : G.Act who, μ.mass (z, act) else 0 by
        by_cases hz : y = z <;> simp [hz])]
    simp
  rw [hsplit, hdelta] at hb
  linarith

end NeutralOccupation

/-- **(N)** Every reachable target-neutral unilateral occupation has
nonpositive actual payoff surplus.  Vacuously true when the polytope is
empty. -/
def IsNeutralOccupationNonpositive (u : A.Config → Payoff ι) : Prop :=
  ∀ (who : ι) (μ : A.NeutralOccupation u who), μ.surplus ≤ 0

/-- A stationary distribution of the prescribed kernel: the set `Ω_σ`. -/
structure PrescribedStationary where
  /-- Stationary mass on configurations. -/
  mass : A.Config → ℝ
  mass_nonneg : ∀ z, 0 ≤ mass z
  balance : ∀ y : A.Config,
    ∑ z : A.Config,
      mass z * ((A.prescribedConfigDist z y).toReal -
        if y = z then 1 else 0) = 0
  total : ∑ z : A.Config, mass z = 1

/-- **(P)** Every prescribed stationary occupation delivers at least the
target. -/
def IsPrescribedDelivery (u : A.Config → Payoff ι) : Prop :=
  ∀ (who : ι) (ν : A.PrescribedStationary),
    0 ≤ ∑ z : A.Config, ν.mass z * (A.prescribedStagePayoff z who - u z who)

/-- The four finite conditions of the credibility criterion.

No field mentions a ledger, a potential, a punishment system, an adaptive
certificate or a deviation-payoff cap. -/
structure IsGlobalCredibilityCriterion (u : A.Config → Payoff ι) : Prop where
  /-- (T0). -/
  targetHarmonic : A.IsPrescribedTargetHarmonic u
  /-- (Ti). -/
  targetSuperharmonic : A.IsUnilateralTargetSuperharmonic u
  /-- (N). -/
  neutralOccupation : A.IsNeutralOccupationNonpositive u
  /-- (P). -/
  prescribedDelivery : A.IsPrescribedDelivery u

/-- The global criterion is invariant under restarting the same closed
architecture at another configuration. -/
theorem IsGlobalCredibilityCriterion.rebase
    {u : A.Config → Payoff ι} (hcrit : A.IsGlobalCredibilityCriterion u)
    (z : A.Config) :
    (A.rebase z).IsGlobalCredibilityCriterion u := by
  refine {
    targetHarmonic := ?_
    targetSuperharmonic := ?_
    neutralOccupation := ?_
    prescribedDelivery := ?_ }
  · intro who y
    simpa only [rebase_prescribedConfigDist_eq] using
      hcrit.targetHarmonic who y
  · intro who y act
    simpa only [rebase_nextConfigDist_eq] using
      hcrit.targetSuperharmonic who y act
  · intro who μ
    let μA : A.NeutralOccupation u who :=
      { mass := μ.mass
        mass_nonneg := μ.mass_nonneg
        neutral_support := by
          intro p hp
          simpa only [rebase_targetCharge_eq] using μ.neutral_support p hp
        balance := by
          intro y
          simpa only [rebase_nextConfigDist_eq] using μ.balance y
        total := μ.total }
    have hsurplus := hcrit.neutralOccupation who μA
    simpa only [NeutralOccupation.surplus, rebase_stagePayoffAt_eq] using
      hsurplus
  · intro who ν
    let νA : A.PrescribedStationary :=
      { mass := ν.mass
        mass_nonneg := ν.mass_nonneg
        balance := by
          intro y
          simpa only [rebase_prescribedConfigDist_eq] using ν.balance y
        total := ν.total }
    have hdelivery := hcrit.prescribedDelivery who νA
    simpa only [rebase_prescribedStagePayoff_eq] using hdelivery

end FiniteUnilateralOccupations

section BasicTargetCharge

variable [Fintype ι] [DecidableEq ι]

-- ---------------------------------------------------------------------------
-- Farkas duality: the conditions produce the bounded potentials
-- ---------------------------------------------------------------------------

/-- Under (Ti) the target charge is nonnegative. -/
theorem targetCharge_nonneg {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonic u) (who : ι) (z : A.Config)
    (act : G.Act who) : 0 ≤ A.targetCharge u who z act := by
  have := hTi who z act
  simp only [targetCharge]
  linarith

end BasicTargetCharge

section MixedTargetRows

variable [Fintype ι] [DecidableEq ι] [∀ i, Finite (G.Act i)]

/-- Mixed form of (Ti). -/
theorem expect_nextConfigDist_target_le {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonic u) (who : ι) (z : A.Config)
    (mixed : PMF (G.Act who)) :
    expect (A.nextConfigDist who z mixed) (fun y => u y who) ≤ u z who := by
  rw [A.expect_nextConfigDist_eq_expect who z mixed]
  calc
    expect mixed
        (fun act => expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => u y who)) ≤
        expect mixed (fun _ => u z who) :=
      expect_mono _ _ _ fun act => hTi who z act
    _ = u z who := expect_const _ _

end MixedTargetRows

section FiniteUnilateralOccupations

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (G.Act i)]

/-- **Farkas step for (N).**  Conditions (Ti) and (N) produce one bounded
configuration potential absorbing every unilateral row of `who`, together
with the finite target-charge constant of (18): the conclusion is exactly
inequality (19), rearranged. -/
theorem exists_deviationPotential {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonic u)
    (hN : A.IsNeutralOccupationNonpositive u) (who : ι) :
    ∃ Φ : A.Config → ℝ, ∀ (z : A.Config) (act : G.Act who),
      A.stagePayoffAt who z (PMF.pure act) +
          expect (A.nextConfigDist who z (PMF.pure act)) Φ ≤
        u z who + Φ z := by
  classical
  letI : DecidablePred
      (fun p : A.Config × G.Act who => A.targetCharge u who p.1 p.2 = 0) :=
    Classical.decPred _
  set kernel : A.Config × G.Act who → PMF A.Config := fun p =>
    if A.targetCharge u who p.1 p.2 = 0 then
      A.nextConfigDist who p.1 (PMF.pure p.2)
    else PMF.pure p.1 with hkernel
  set source : A.Config × G.Act who → A.Config := fun p => p.1 with hsource
  set charge : A.Config × G.Act who → ℝ := fun p =>
    if A.targetCharge u who p.1 p.2 = 0 then
      A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who
    else 0 with hcharge
  -- Off the neutral set the modified occupation column vanishes identically.
  have hoff : ∀ p : A.Config × G.Act who,
      A.targetCharge u who p.1 p.2 ≠ 0 →
        ∀ y : A.Config, actualOccupationColumn kernel source p y = 0 := by
    intro p hp y
    simp [actualOccupationColumn, hkernel, hsource, hp, PMF.pure_apply,
      apply_ite ENNReal.toReal]
  have halt :=
    normalizedPositiveChargedCirculation_xor_driftPotential
      kernel source charge
  rw [xor_def] at halt
  have hpotential : ∃ ξ : A.Config → ℝ, ∀ p : A.Config × G.Act who,
      charge p ≤ expect (kernel p) ξ - ξ (source p) := by
    rcases halt with ⟨hcirc, -⟩ | ⟨hpot, -⟩
    · exfalso
      obtain ⟨mass, hmass, hbalance, htotal⟩ := hcirc
      set restricted : A.Config × G.Act who → ℝ := fun p =>
        if A.targetCharge u who p.1 p.2 = 0 then mass p else 0
        with hrestricted
      have hrestricted_nonneg : ∀ p, 0 ≤ restricted p := by
        intro p
        by_cases hp : A.targetCharge u who p.1 p.2 = 0 <;>
          simp [hrestricted, hp, hmass p]
      have hterm : ∀ (p : A.Config × G.Act who) (y : A.Config),
          restricted p *
              ((A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal -
                if y = p.1 then 1 else 0) =
            mass p * actualOccupationColumn kernel source p y := by
        intro p y
        by_cases hp : A.targetCharge u who p.1 p.2 = 0
        · simp [hrestricted, hp, actualOccupationColumn, hkernel, hsource]
        · simp [hrestricted, hp, hoff p hp y]
      have hbalance' : ∀ y : A.Config,
          ∑ p : A.Config × G.Act who, restricted p *
            ((A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal -
              if y = p.1 then 1 else 0) = 0 := by
        intro y
        rw [Finset.sum_congr rfl fun p _ => hterm p y]
        exact hbalance y
      have hsurplus :
          ∑ p : A.Config × G.Act who, restricted p *
            (A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who) = 1 := by
        rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) =>
          show restricted p *
              (A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who) =
            mass p * charge p by
            by_cases hp : A.targetCharge u who p.1 p.2 = 0
            · simp [hrestricted, hcharge, hp]
            · simp [hrestricted, hcharge, hp]]
        exact htotal
      have hSnonneg : 0 ≤ ∑ p : A.Config × G.Act who, restricted p :=
        Finset.sum_nonneg fun p _ => hrestricted_nonneg p
      have hSpos : 0 < ∑ p : A.Config × G.Act who, restricted p := by
        rcases hSnonneg.lt_or_eq with hlt | heq
        · exact hlt
        · exfalso
          have hzero : ∀ p : A.Config × G.Act who, restricted p = 0 :=
            fun p => (Finset.sum_eq_zero_iff_of_nonneg
              fun q _ => hrestricted_nonneg q).1 heq.symm p (Finset.mem_univ p)
          have hz : ∑ p : A.Config × G.Act who, restricted p *
              (A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who) = 0 :=
            Finset.sum_eq_zero fun p _ => by rw [hzero p]; ring
          linarith
      have hbad : (∑ p : A.Config × G.Act who,
          restricted p / (∑ q : A.Config × G.Act who, restricted q) *
            (A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who)) ≤ 0 :=
        hN who
        { mass := fun p => restricted p / (∑ q : A.Config × G.Act who,
            restricted q)
          mass_nonneg := fun p => div_nonneg (hrestricted_nonneg p) hSpos.le
          neutral_support := by
            intro p hp
            by_contra hne
            have hzero : restricted p = 0 := by rw [hrestricted]; simp [hne]
            rw [hzero, zero_div] at hp
            exact absurd hp (lt_irrefl 0)
          balance := by
            intro y
            have hb := hbalance' y
            calc
              ∑ p : A.Config × G.Act who,
                  restricted p /
                      (∑ q : A.Config × G.Act who, restricted q) *
                    ((A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal -
                      if y = p.1 then 1 else 0) =
                  (∑ p : A.Config × G.Act who, restricted p *
                    ((A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal -
                      if y = p.1 then 1 else 0)) /
                    (∑ q : A.Config × G.Act who, restricted q) := by
                    rw [Finset.sum_div]
                    exact Finset.sum_congr rfl fun p _ => by ring
              _ = 0 := by rw [hb, zero_div]
          total := by
            rw [← Finset.sum_div]
            exact div_self (ne_of_gt hSpos) }
      have hcalc : (∑ p : A.Config × G.Act who,
          restricted p / (∑ q : A.Config × G.Act who, restricted q) *
            (A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who)) =
          (∑ p : A.Config × G.Act who, restricted p *
            (A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who)) /
            (∑ q : A.Config × G.Act who, restricted q) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun p _ => by ring
      rw [hcalc, hsurplus] at hbad
      have hone : (0 : ℝ) < 1 / (∑ q : A.Config × G.Act who, restricted q) :=
        div_pos zero_lt_one hSpos
      linarith
    · exact hpot
  obtain ⟨ξ, hξ⟩ := hpotential
  -- The neutral inequality, restated on the actual kernel.
  have hneutral : ∀ (z : A.Config) (act : G.Act who),
      A.targetCharge u who z act = 0 →
        A.stagePayoffAt who z (PMF.pure act) - u z who ≤
          expect (A.nextConfigDist who z (PMF.pure act)) ξ - ξ z := by
    intro z act hz
    have hp := hξ (z, act)
    simpa [hcharge, hkernel, hsource, hz] using hp
  -- The finite target-charge constant of (18).
  set gap : A.Config × G.Act who → ℝ := fun p =>
    A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who -
      (expect (A.nextConfigDist who p.1 (PMF.pure p.2)) ξ - ξ p.1) with hgap
  set ratio : A.Config × G.Act who → ℝ := fun p =>
    if A.targetCharge u who p.1 p.2 = 0 then 0
    else gap p / A.targetCharge u who p.1 p.2 with hratio
  have hratio_le : ∀ p, ratio p ≤ ∑ q : A.Config × G.Act who, |ratio q| := by
    intro p
    calc
      ratio p ≤ |ratio p| := le_abs_self _
      _ ≤ ∑ q : A.Config × G.Act who, |ratio q| :=
          Finset.single_le_sum (f := fun q => |ratio q|)
            (fun q _ => abs_nonneg _) (Finset.mem_univ p)
  have hgap_le : ∀ p : A.Config × G.Act who,
      gap p ≤ (∑ q : A.Config × G.Act who, |ratio q|) *
        A.targetCharge u who p.1 p.2 := by
    intro p
    by_cases hp : A.targetCharge u who p.1 p.2 = 0
    · have hn := hneutral p.1 p.2 hp
      rw [hp, mul_zero, hgap]
      simp only
      linarith
    · have hpos : 0 < A.targetCharge u who p.1 p.2 :=
        lt_of_le_of_ne (A.targetCharge_nonneg hTi who p.1 p.2) (Ne.symm hp)
      have hr : ratio p = gap p / A.targetCharge u who p.1 p.2 := by
        rw [hratio]; simp [hp]
      have hle := hratio_le p
      rw [hr, div_le_iff₀ hpos] at hle
      exact hle
  refine ⟨fun z => (∑ q : A.Config × G.Act who, |ratio q|) * u z who - ξ z, ?_⟩
  intro z act
  have hgapz := hgap_le (z, act)
  rw [hgap] at hgapz
  simp only [targetCharge] at hgapz
  have hsplit :
      expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => (∑ q : A.Config × G.Act who, |ratio q|) * u y who -
            ξ y) =
        (∑ q : A.Config × G.Act who, |ratio q|) *
            expect (A.nextConfigDist who z (PMF.pure act))
              (fun y => u y who) -
          expect (A.nextConfigDist who z (PMF.pure act)) ξ := by
    rw [expect_sub, expect_const_mul]
  rw [hsplit]
  linarith

end FiniteUnilateralOccupations

section PrescribedOccupations

variable [Fintype ι]

/-- **Farkas step for (P).**  Condition (P) produces the bounded
prescribed-play potential of (21). -/
theorem exists_deliveryPotential {u : A.Config → Payoff ι}
    (hP : A.IsPrescribedDelivery u) (who : ι) :
    ∃ Ψ : A.Config → ℝ, ∀ z : A.Config,
      u z who + Ψ z ≤
        A.prescribedStagePayoff z who +
          expect (A.prescribedConfigDist z) Ψ := by
  classical
  have halt :=
    normalizedPositiveChargedCirculation_xor_driftPotential
      A.prescribedConfigDist (fun z : A.Config => z)
      (fun z => u z who - A.prescribedStagePayoff z who)
  rw [xor_def] at halt
  rcases halt with ⟨hcirc, -⟩ | ⟨hpot, -⟩
  · exfalso
    obtain ⟨mass, hmass, hbalance, htotal⟩ := hcirc
    have hb : ∀ y : A.Config, ∑ z : A.Config, mass z *
        ((A.prescribedConfigDist z y).toReal -
          if y = z then 1 else 0) = 0 := hbalance
    have hSnonneg : 0 ≤ ∑ z : A.Config, mass z :=
      Finset.sum_nonneg fun z _ => hmass z
    have hSpos : 0 < ∑ z : A.Config, mass z := by
      rcases hSnonneg.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hzero : ∀ z : A.Config, mass z = 0 := fun z =>
          (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hmass q).1
            heq.symm z (Finset.mem_univ z)
        have hz : ∑ z : A.Config, mass z *
            (u z who - A.prescribedStagePayoff z who) = 0 :=
          Finset.sum_eq_zero fun z _ => by rw [hzero z]; ring
        linarith
    have hdelivery : 0 ≤ ∑ z : A.Config,
        mass z / (∑ y : A.Config, mass y) *
          (A.prescribedStagePayoff z who - u z who) :=
      hP who
      { mass := fun z => mass z / (∑ y : A.Config, mass y)
        mass_nonneg := fun z => div_nonneg (hmass z) hSpos.le
        balance := by
          intro y
          calc
            ∑ z : A.Config, mass z / (∑ w : A.Config, mass w) *
                ((A.prescribedConfigDist z y).toReal -
                  if y = z then 1 else 0) =
                (∑ z : A.Config, mass z *
                  ((A.prescribedConfigDist z y).toReal -
                    if y = z then 1 else 0)) /
                  (∑ w : A.Config, mass w) := by
                  rw [Finset.sum_div]
                  exact Finset.sum_congr rfl fun z _ => by ring
            _ = 0 := by rw [hb y, zero_div]
        total := by
          rw [← Finset.sum_div]
          exact div_self (ne_of_gt hSpos) }
    have hcalc : (∑ z : A.Config, mass z / (∑ w : A.Config, mass w) *
        (A.prescribedStagePayoff z who - u z who)) =
        -((∑ z : A.Config, mass z *
          (u z who - A.prescribedStagePayoff z who)) /
            (∑ w : A.Config, mass w)) := by
      rw [← neg_div, ← Finset.sum_neg_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [hcalc, htotal] at hdelivery
    have hone : (0 : ℝ) < 1 / (∑ w : A.Config, mass w) :=
      div_pos zero_lt_one hSpos
    linarith
  · obtain ⟨Ψ, hΨ⟩ := hpot
    refine ⟨Ψ, fun z => ?_⟩
    have hz : u z who - A.prescribedStagePayoff z who ≤
        expect (A.prescribedConfigDist z) Ψ - Ψ z := hΨ z
    linarith

end PrescribedOccupations

-- ---------------------------------------------------------------------------
-- The induced public phase profile
-- ---------------------------------------------------------------------------

/-- The public configuration reached after a finite public history. -/
def configAt (arch : G.FiniteResponseArchitecture initial) :
    (t : ℕ) → G.Hist t → arch.Config
  | 0, _ => arch.start
  | t + 1, h =>
      arch.step (configAt arch t (Fin.init h.1, (h.1 (Fin.last t)).1))
        (h.1 (Fin.last t)).2 h.2

@[simp] theorem configAt_zero (h : G.Hist 0) : A.configAt 0 h = A.start := rfl

theorem configAt_snoc {t : ℕ} (h : G.Hist t) (act : G.JointAct)
    (s' : G.State) :
    A.configAt (t + 1) ((Fin.snoc h.1 (h.2, act), s') : G.Hist (t + 1)) =
      A.step (A.configAt t h) act s' := by
  simp [configAt]

theorem publicState_configAt_succ {t : ℕ} (h : G.Hist (t + 1)) :
    A.publicState (A.configAt (t + 1) h) = h.2 := by
  simp only [configAt]
  rw [A.step_publicState]

theorem publicState_configAt_emptyHist :
    A.publicState (A.configAt 0 (G.emptyHist initial)) =
      (G.emptyHist initial).2 := by
  simpa [emptyHist] using A.start_publicState

/-- The public-phase profile implemented by the architecture. -/
def phaseProfile : G.PublicPhaseProfile where
  Phase := A.Config
  phase := A.configAt
  play := A.play

@[simp] theorem phaseProfile_behaviorProfile (i : ι) (t : ℕ) (h : G.Hist t) :
    A.phaseProfile.behaviorProfile i t h = A.play (A.configAt t h) i := rfl

section PrescribedActionLaw

variable [Fintype ι]

theorem stageActionDist_prescribed {t : ℕ} (h : G.Hist t) :
    G.stageActionDist A.phaseProfile.behaviorProfile h =
      A.prescribedActionDist (A.configAt t h) := rfl

end PrescribedActionLaw

section UnilateralActionLaw

variable [Fintype ι] [DecidableEq ι]

theorem stageActionDist_update (who : ι) (dev : G.BehaviorStrategy who)
    {t : ℕ} (h : G.Hist t) :
    G.stageActionDist
        (Function.update A.phaseProfile.behaviorProfile who dev) h =
      A.actionDist who (A.configAt t h) (dev t h) := by
  unfold StochasticGame.stageActionDist actionDist
  congr 1
  funext i
  by_cases hi : i = who
  · subst hi; simp
  · simp [Function.update_of_ne hi]

end UnilateralActionLaw

section UnilateralStagePayoffLaw

variable [Fintype ι] [DecidableEq ι]

theorem stageEUAt_update (who : ι) (dev : G.BehaviorStrategy who) {t : ℕ}
    (h : G.Hist t) (hstate : A.publicState (A.configAt t h) = h.2) :
    G.stageEUAt (Function.update A.phaseProfile.behaviorProfile who dev)
        h who =
      A.stagePayoffAt who (A.configAt t h) (dev t h) := by
  unfold StochasticGame.stageEUAt stagePayoffAt
  rw [A.stageActionDist_update who dev h, hstate]

end UnilateralStagePayoffLaw

section PrescribedStagePayoffLaw

variable [Fintype ι]

theorem stageEUAt_prescribed (who : ι) {t : ℕ} (h : G.Hist t)
    (hstate : A.publicState (A.configAt t h) = h.2) :
    G.stageEUAt A.phaseProfile.behaviorProfile h who =
      A.prescribedStagePayoff (A.configAt t h) who := by
  unfold StochasticGame.stageEUAt prescribedStagePayoff
  rw [A.stageActionDist_prescribed h, hstate]

end PrescribedStagePayoffLaw

section ContinuationShape

variable [Fintype ι]

theorem historyContinuationEU_eq (σ : G.BehaviorProfile)
    (f : A.Config → ℝ) {t : ℕ} (h : G.Hist t) :
    G.historyContinuationEU σ (fun t h => f (A.configAt t h)) h =
      expect (G.stageActionDist σ h) fun act =>
        expect (G.transition h.2 act) fun s' =>
          f (A.step (A.configAt t h) act s') :=
  congrArg _ (funext fun act => congrArg _ (funext fun s' =>
    congrArg f (A.configAt_snoc h act s')))

end ContinuationShape

section ContinuationLaws

variable [Fintype ι] [DecidableEq ι]

theorem historyContinuationEU_update (who : ι)
    (dev : G.BehaviorStrategy who) (f : A.Config → ℝ) {t : ℕ}
    (h : G.Hist t) (hstate : A.publicState (A.configAt t h) = h.2) :
    G.historyContinuationEU
        (Function.update A.phaseProfile.behaviorProfile who dev)
        (fun t h => f (A.configAt t h)) h =
      expect (A.nextConfigDist who (A.configAt t h) (dev t h)) f := by
  rw [A.historyContinuationEU_eq _ f h,
    A.expect_nextConfigDist who (A.configAt t h) (dev t h) f,
    A.stageActionDist_update who dev h, hstate]

end ContinuationLaws

section PrescribedContinuationLaw

variable [Fintype ι]

theorem historyContinuationEU_prescribed (f : A.Config → ℝ) {t : ℕ}
    (h : G.Hist t) (hstate : A.publicState (A.configAt t h) = h.2) :
    G.historyContinuationEU A.phaseProfile.behaviorProfile
        (fun t h => f (A.configAt t h)) h =
      expect (A.prescribedConfigDist (A.configAt t h)) f := by
  rw [A.historyContinuationEU_eq _ f h,
    A.expect_prescribedConfigDist (A.configAt t h) f,
    A.stageActionDist_prescribed h, hstate]

end PrescribedContinuationLaw

/-- A crude but uniform bound on a configuration potential. -/
def configBound (f : A.Config → ℝ) : ℝ := ∑ z : A.Config, |f z|

theorem configBound_nonneg (f : A.Config → ℝ) : 0 ≤ A.configBound f :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_configBound (f : A.Config → ℝ) (z : A.Config) :
    |f z| ≤ A.configBound f :=
  Finset.single_le_sum (f := fun y => |f y|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ z)

section ExpectedConfigurationBound

variable [Fintype ι]

/-- Expectations of a configuration potential are bounded by its finite
ambient `ℓ¹` bound. -/
theorem abs_expectedHistoryValue_le_configBound (σ : G.BehaviorProfile)
    (f : A.Config → ℝ) (t : ℕ) :
    |G.expectedHistoryValue σ initial
      (fun t h => f (A.configAt t h)) t| ≤ A.configBound f :=
  abs_expect_le_of_abs_le _ _ fun _ => A.abs_le_configBound f _

end ExpectedConfigurationBound

section HistoryBounds

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

-- ---------------------------------------------------------------------------
-- Target processes along the realized history
-- ---------------------------------------------------------------------------

/-- Expected target after `t` stages is nonincreasing under a unilateral
deviation: the supermartingale content of (Ti). -/
theorem expectedTarget_update_le {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonic u) (who : ι)
    (dev : G.BehaviorStrategy who) (t : ℕ) :
    G.expectedHistoryValue
        (Function.update A.phaseProfile.behaviorProfile who dev) initial
        (fun t h => u (A.configAt t h) who) t ≤ u A.start who := by
  induction t with
  | zero => simp [expectedHistoryValue]
  | succ n ih =>
      refine le_trans ?_ ih
      rw [G.expectedHistoryValue_succ]
      refine expect_histDist_le_of_succ _ initial
        (fun t h => G.historyContinuationEU
          (Function.update A.phaseProfile.behaviorProfile who dev)
          (fun t h => u (A.configAt t h) who) h)
        (fun t h => u (A.configAt t h) who) ?_ ?_ n
      · rw [A.historyContinuationEU_update who dev (fun y => u y who) _
          A.publicState_configAt_emptyHist]
        exact A.expect_nextConfigDist_target_le hTi who _ _
      · intro m h
        rw [A.historyContinuationEU_update who dev (fun y => u y who) h
          (A.publicState_configAt_succ h)]
        exact A.expect_nextConfigDist_target_le hTi who _ _

end HistoryBounds

section PrescribedTargetHistory

variable [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]

/-- Expected target after `t` stages is constant under prescribed play: the
martingale content of (T0). -/
theorem expectedTarget_prescribed_eq {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonic u) (who : ι) (t : ℕ) :
    G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
        (fun t h => u (A.configAt t h) who) t = u A.start who := by
  induction t with
  | zero => simp [expectedHistoryValue]
  | succ n ih =>
      rw [← ih, G.expectedHistoryValue_succ]
      refine expect_histDist_congr_of_succ _ initial
        (fun t h => G.historyContinuationEU A.phaseProfile.behaviorProfile
          (fun t h => u (A.configAt t h) who) h)
        (fun t h => u (A.configAt t h) who) ?_ ?_ n
      · rw [A.historyContinuationEU_prescribed (fun y => u y who) _
          A.publicState_configAt_emptyHist]
        exact hT0 who _
      · intro m h
        rw [A.historyContinuationEU_prescribed (fun y => u y who) h
          (A.publicState_configAt_succ h)]
        exact hT0 who _

end PrescribedTargetHistory

section HistoryBounds

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

-- ---------------------------------------------------------------------------
-- Payoff bounds
-- ---------------------------------------------------------------------------

/-- **Deviation cap.**  Under (Ti) and the deviation potential, every
unilateral behavior deviation earns at most the target plus an `O(1/T)`
remainder, uniformly in the deviation. -/
theorem finiteAveragePayoff_update_le {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonic u) (who : ι)
    (Φ : A.Config → ℝ)
    (hΦ : ∀ (z : A.Config) (act : G.Act who),
      A.stagePayoffAt who z (PMF.pure act) +
          expect (A.nextConfigDist who z (PMF.pure act)) Φ ≤ u z who + Φ z)
    (dev : G.BehaviorStrategy who) {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff initial T
        (Function.update A.phaseProfile.behaviorProfile who dev) who ≤
      u A.start who + 2 * A.configBound Φ / T := by
  have hΦmix : ∀ (z : A.Config) (mixed : PMF (G.Act who)),
      A.stagePayoffAt who z mixed +
          expect (A.nextConfigDist who z mixed) Φ ≤ u z who + Φ z := by
    intro z mixed
    rw [A.stagePayoffAt_eq_expect who z mixed,
      A.expect_nextConfigDist_eq_expect who z mixed Φ, ← expect_add]
    calc
      expect mixed (fun act => A.stagePayoffAt who z (PMF.pure act) +
          expect (A.nextConfigDist who z (PMF.pure act)) Φ) ≤
          expect mixed (fun _ => u z who + Φ z) :=
        expect_mono _ _ _ fun act => hΦ z act
      _ = u z who + Φ z := expect_const _ _
  have hstep : ∀ t : ℕ,
      G.expectedStagePayoff
            (Function.update A.phaseProfile.behaviorProfile who dev)
            initial t who +
          G.expectedHistoryValue
            (Function.update A.phaseProfile.behaviorProfile who dev) initial
            (fun t h => Φ (A.configAt t h)) (t + 1) ≤
        G.expectedHistoryValue
            (Function.update A.phaseProfile.behaviorProfile who dev) initial
            (fun t h => u (A.configAt t h) who) t +
          G.expectedHistoryValue
            (Function.update A.phaseProfile.behaviorProfile who dev) initial
            (fun t h => Φ (A.configAt t h)) t := by
    intro t
    have hleft :
        G.expectedStagePayoff
              (Function.update A.phaseProfile.behaviorProfile who dev)
              initial t who +
            G.expectedHistoryValue
              (Function.update A.phaseProfile.behaviorProfile who dev) initial
              (fun t h => Φ (A.configAt t h)) (t + 1) =
          expect (G.histDist
              (Function.update A.phaseProfile.behaviorProfile who dev)
              initial t)
            (fun h =>
              G.stageEUAt
                  (Function.update A.phaseProfile.behaviorProfile who dev)
                  h who +
                G.historyContinuationEU
                  (Function.update A.phaseProfile.behaviorProfile who dev)
                  (fun t h => Φ (A.configAt t h)) h) := by
      rw [G.expectedHistoryValue_succ]
      exact (expect_add _ _ _).symm
    have hright :
        G.expectedHistoryValue
              (Function.update A.phaseProfile.behaviorProfile who dev) initial
              (fun t h => u (A.configAt t h) who) t +
            G.expectedHistoryValue
              (Function.update A.phaseProfile.behaviorProfile who dev) initial
              (fun t h => Φ (A.configAt t h)) t =
          expect (G.histDist
              (Function.update A.phaseProfile.behaviorProfile who dev)
              initial t)
            (fun h => u (A.configAt t h) who + Φ (A.configAt t h)) :=
      (expect_add _ _ _).symm
    rw [hleft, hright]
    refine expect_histDist_le_of_succ _ initial
      (fun t h =>
        G.stageEUAt (Function.update A.phaseProfile.behaviorProfile who dev)
            h who +
          G.historyContinuationEU
            (Function.update A.phaseProfile.behaviorProfile who dev)
            (fun t h => Φ (A.configAt t h)) h)
      (fun t h => u (A.configAt t h) who + Φ (A.configAt t h)) ?_ ?_ t
    · rw [A.stageEUAt_update who dev _ A.publicState_configAt_emptyHist,
        A.historyContinuationEU_update who dev _ _
          A.publicState_configAt_emptyHist]
      exact hΦmix _ _
    · intro m h
      rw [A.stageEUAt_update who dev _ (A.publicState_configAt_succ h),
        A.historyContinuationEU_update who dev _ _
          (A.publicState_configAt_succ h)]
      exact hΦmix _ _
  have htel := sumStep_telescope_le hstep T
  have hsumU :
      (∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update A.phaseProfile.behaviorProfile who dev) initial
            (fun t h => u (A.configAt t h) who) t) ≤
        (T : ℝ) * u A.start who := by
    calc
      (∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update A.phaseProfile.behaviorProfile who dev) initial
            (fun t h => u (A.configAt t h) who) t) ≤
          ∑ _t ∈ Finset.range T, u A.start who :=
        Finset.sum_le_sum fun t _ => A.expectedTarget_update_le hTi who dev t
      _ = (T : ℝ) * u A.start who := by simp
  have hW0 :
      G.expectedHistoryValue
          (Function.update A.phaseProfile.behaviorProfile who dev) initial
          (fun t h => Φ (A.configAt t h)) 0 ≤ A.configBound Φ :=
    le_of_abs_le (A.abs_expectedHistoryValue_le_configBound _ Φ 0)
  have hWT : -A.configBound Φ ≤
      G.expectedHistoryValue
        (Function.update A.phaseProfile.behaviorProfile who dev) initial
        (fun t h => Φ (A.configAt t h)) T := by
    have habs := A.abs_expectedHistoryValue_le_configBound
      (Function.update A.phaseProfile.behaviorProfile who dev) Φ T
    rw [abs_le] at habs
    exact habs.1
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTreal
  have hraw :
      (∑ t ∈ Finset.range T,
          G.expectedStagePayoff
            (Function.update A.phaseProfile.behaviorProfile who dev)
            initial t who) ≤
        (T : ℝ) * u A.start who + 2 * A.configBound Φ := by
    linarith
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rw [show u A.start who + 2 * A.configBound Φ / (T : ℝ) =
      ((T : ℝ) * u A.start who + 2 * A.configBound Φ) / (T : ℝ) by
    field_simp]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hraw (by positivity)

/-- **Prescribed upper bound.**  Prescribed play is the special deviation
that keeps the prescribed row. -/
theorem finiteAveragePayoff_prescribed_le {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonic u) (who : ι)
    (Φ : A.Config → ℝ)
    (hΦ : ∀ (z : A.Config) (act : G.Act who),
      A.stagePayoffAt who z (PMF.pure act) +
          expect (A.nextConfigDist who z (PMF.pure act)) Φ ≤ u z who + Φ z)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff initial T A.phaseProfile.behaviorProfile who ≤
      u A.start who + 2 * A.configBound Φ / T := by
  have h := A.finiteAveragePayoff_update_le hTi who Φ hΦ
    (A.phaseProfile.behaviorProfile who) hT
  rwa [Function.update_eq_self] at h

end HistoryBounds

section PrescribedDeliveryBounds

variable [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]

/-- **Prescribed delivery.**  Under (T0) and the delivery potential,
prescribed play delivers the target up to an `O(1/T)` remainder. -/
theorem le_finiteAveragePayoff_prescribed {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonic u) (who : ι) (Ψ : A.Config → ℝ)
    (hΨ : ∀ z : A.Config,
      u z who + Ψ z ≤
        A.prescribedStagePayoff z who +
          expect (A.prescribedConfigDist z) Ψ)
    {T : ℕ} (hT : 0 < T) :
    u A.start who - 2 * A.configBound Ψ / T ≤
      G.finiteAveragePayoff initial T A.phaseProfile.behaviorProfile who := by
  have hstep : ∀ t : ℕ,
      G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => u (A.configAt t h) who) t +
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => Ψ (A.configAt t h)) t ≤
        G.expectedStagePayoff A.phaseProfile.behaviorProfile initial t who +
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => Ψ (A.configAt t h)) (t + 1) := by
    intro t
    have hleft :
        G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
              (fun t h => u (A.configAt t h) who) t +
            G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
              (fun t h => Ψ (A.configAt t h)) t =
          expect (G.histDist A.phaseProfile.behaviorProfile initial t)
            (fun h => u (A.configAt t h) who + Ψ (A.configAt t h)) :=
      (expect_add _ _ _).symm
    have hright :
        G.expectedStagePayoff A.phaseProfile.behaviorProfile initial t who +
            G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
              (fun t h => Ψ (A.configAt t h)) (t + 1) =
          expect (G.histDist A.phaseProfile.behaviorProfile initial t)
            (fun h =>
              G.stageEUAt A.phaseProfile.behaviorProfile h who +
                G.historyContinuationEU A.phaseProfile.behaviorProfile
                  (fun t h => Ψ (A.configAt t h)) h) := by
      rw [G.expectedHistoryValue_succ]
      exact (expect_add _ _ _).symm
    rw [hleft, hright]
    refine expect_histDist_le_of_succ _ initial
      (fun t h => u (A.configAt t h) who + Ψ (A.configAt t h))
      (fun t h =>
        G.stageEUAt A.phaseProfile.behaviorProfile h who +
          G.historyContinuationEU A.phaseProfile.behaviorProfile
            (fun t h => Ψ (A.configAt t h)) h) ?_ ?_ t
    · rw [A.stageEUAt_prescribed who _ A.publicState_configAt_emptyHist,
        A.historyContinuationEU_prescribed _ _
          A.publicState_configAt_emptyHist]
      exact hΨ _
    · intro m h
      rw [A.stageEUAt_prescribed who _ (A.publicState_configAt_succ h),
        A.historyContinuationEU_prescribed _ _
          (A.publicState_configAt_succ h)]
      exact hΨ _
  have htel := sumStep_telescope_ge hstep T
  have hsumU :
      (∑ t ∈ Finset.range T,
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => u (A.configAt t h) who) t) =
        (T : ℝ) * u A.start who := by
    rw [Finset.sum_congr rfl fun t _ =>
      A.expectedTarget_prescribed_eq hT0 who t]
    simp
  have hW0 : -A.configBound Ψ ≤
      G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
        (fun t h => Ψ (A.configAt t h)) 0 := by
    have habs := A.abs_expectedHistoryValue_le_configBound
      A.phaseProfile.behaviorProfile Ψ 0
    rw [abs_le] at habs
    exact habs.1
  have hWT :
      G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
        (fun t h => Ψ (A.configAt t h)) T ≤ A.configBound Ψ :=
    le_of_abs_le (A.abs_expectedHistoryValue_le_configBound _ Ψ T)
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTreal
  have hraw : (T : ℝ) * u A.start who - 2 * A.configBound Ψ ≤
      ∑ t ∈ Finset.range T,
        G.expectedStagePayoff A.phaseProfile.behaviorProfile initial t who := by
    rw [hsumU] at htel
    linarith
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rw [show u A.start who - 2 * A.configBound Ψ / (T : ℝ) =
      ((T : ℝ) * u A.start who - 2 * A.configBound Ψ) / (T : ℝ) by
    field_simp]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hraw (by positivity)

end PrescribedDeliveryBounds

section HistoryBounds

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Fintype (G.Act i)]

-- ---------------------------------------------------------------------------
-- The criterion direction
-- ---------------------------------------------------------------------------

/-- **Quantitative criterion direction.**  The four finite conditions
produce one explicit modulus that simultaneously governs prescribed
delivery and every unilateral deviation, at every horizon.

This is the finite-horizon form of (13)–(15): the residual budget is
`O(1)`, hence the per-stage remainder is `O(1/T)`, uniformly in `T` and in
the deviation. -/
theorem exists_uniformModulus_of_isGlobalCredibilityCriterion
    {u : A.Config → Payoff ι} (hcrit : A.IsGlobalCredibilityCriterion u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (who : ι) (T : ℕ), 0 < T →
      |G.finiteAveragePayoff initial T A.phaseProfile.behaviorProfile who -
          u A.start who| ≤ M / T ∧
        ∀ dev : G.BehaviorStrategy who,
          G.finiteAveragePayoff initial T
              (Function.update A.phaseProfile.behaviorProfile who dev)
              who ≤ u A.start who + M / T := by
  classical
  choose Φ hΦ using fun who =>
    A.exists_deviationPotential hcrit.targetSuperharmonic
      hcrit.neutralOccupation who
  choose Ψ hΨ using fun who =>
    A.exists_deliveryPotential hcrit.prescribedDelivery who
  refine ⟨∑ who : ι, (2 * A.configBound (Φ who) + 2 * A.configBound (Ψ who)),
    Finset.sum_nonneg fun who _ => by
      have h1 := A.configBound_nonneg (Φ who)
      have h2 := A.configBound_nonneg (Ψ who)
      linarith, ?_⟩
  intro who T hT
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hpick : 2 * A.configBound (Φ who) + 2 * A.configBound (Ψ who) ≤
      ∑ w : ι, (2 * A.configBound (Φ w) + 2 * A.configBound (Ψ w)) :=
    Finset.single_le_sum
      (f := fun w => 2 * A.configBound (Φ w) + 2 * A.configBound (Ψ w))
      (fun w _ => by
        have h1 := A.configBound_nonneg (Φ w)
        have h2 := A.configBound_nonneg (Ψ w)
        linarith)
      (Finset.mem_univ who)
  have hΦ0 := A.configBound_nonneg (Φ who)
  have hΨ0 := A.configBound_nonneg (Ψ who)
  have hΦle : 2 * A.configBound (Φ who) ≤
      ∑ w : ι, (2 * A.configBound (Φ w) + 2 * A.configBound (Ψ w)) := by
    linarith
  have hΨle : 2 * A.configBound (Ψ who) ≤
      ∑ w : ι, (2 * A.configBound (Φ w) + 2 * A.configBound (Ψ w)) := by
    linarith
  have hΦdiv := (div_le_div_iff_of_pos_right hTreal).2 hΦle
  have hΨdiv := (div_le_div_iff_of_pos_right hTreal).2 hΨle
  have hupper := A.finiteAveragePayoff_prescribed_le
    hcrit.targetSuperharmonic who (Φ who) (hΦ who) hT
  have hlower := A.le_finiteAveragePayoff_prescribed
    hcrit.targetHarmonic who (Ψ who) (hΨ who) hT
  refine ⟨?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith
  · intro dev
    have hdev := A.finiteAveragePayoff_update_le hcrit.targetSuperharmonic
      who (Φ who) (hΦ who) dev hT
    linarith

/-- **The criterion direction.**  For a fixed finite closed response
architecture and a complete target assignment satisfying (T0), (Ti), (N)
and (P), the tree's operational public-response enforcement ledger exists
at every positive error.

This is the missing producer: `PublicResponseEnforcementLedgerAt` is the
exact structure consumed by
`PublicResponseEnforcementLedgerAt.toIsPublicPhasePunishmentSystemAt` and
`…toIsAdaptivePotentialCertificateAt`. -/
theorem nonempty_publicResponseEnforcementLedgerAt
    {u : A.Config → Payoff ι} (hcrit : A.IsGlobalCredibilityCriterion u)
    (v : Payoff ι) (hv : ∀ who, u A.start who = v who)
    {err : ℝ} (herr : 0 < err) :
    Nonempty
      (G.PublicResponseEnforcementLedgerAt A.phaseProfile initial v err) := by
  classical
  obtain ⟨M, hM, hbounds⟩ :=
    A.exists_uniformModulus_of_isGlobalCredibilityCriterion hcrit
  have hstep : ∀ total : ℕ, max 2 ⌈M / err⌉₊ ≤ total →
      0 < total ∧ M / (total : ℝ) ≤ err := by
    intro total htotal
    have htwo : 2 ≤ total := le_trans (le_max_left _ _) htotal
    have htotal_pos : 0 < total := by omega
    have htotal_real : (0 : ℝ) < total := by exact_mod_cast htotal_pos
    have hceil : (⌈M / err⌉₊ : ℝ) ≤ (total : ℝ) := by
      exact_mod_cast le_trans (le_max_right 2 _) htotal
    have hMdiv : M / err ≤ (total : ℝ) := le_trans (Nat.le_ceil _) hceil
    refine ⟨htotal_pos, ?_⟩
    rw [div_le_iff₀ htotal_real]
    have hmul := (div_le_iff₀ herr).1 hMdiv
    linarith
  refine ⟨{
    horizon := max 2 ⌈M / err⌉₊
    lowerLoss := fun who _ h =>
      v who - G.stageEUAt A.phaseProfile.behaviorProfile h who
    upperLoss := fun who _ h =>
      G.stageEUAt A.phaseProfile.behaviorProfile h who - v who
    monitoringResidual := fun _ _ _ _ => 0
    continuationResidual := fun who dev _ h =>
      G.stageEUAt
        (Function.update A.phaseProfile.behaviorProfile who dev) h who -
          v who
    monitoringError := 0
    continuationError := err
    error_nonneg := herr.le
    horizon_ge_two := le_max_left _ _
    lower_stage := by intro i t h; linarith
    upper_stage := by intro i t h; linarith
    deviation_stage := by intro i dev t h; linarith
    lowerLoss_cesaro := ?_
    upperLoss_cesaro := ?_
    monitoringResidual_cesaro := by
      intro who dev total htotal
      simp [expectedHistoryValue]
    continuationResidual_cesaro := ?_
    deviation_budget := by linarith }⟩
  · intro who total htotal
    obtain ⟨htotal_pos, hMerr⟩ := hstep total htotal
    rw [G.inv_mul_sum_expectedHistoryValue_sub_stageEUAt
      A.phaseProfile.behaviorProfile initial who (v who) htotal_pos]
    obtain ⟨habs, -⟩ := hbounds who total htotal_pos
    rw [abs_le] at habs
    have hlow := habs.1
    rw [hv who] at hlow
    linarith
  · intro who total htotal
    obtain ⟨htotal_pos, hMerr⟩ := hstep total htotal
    rw [G.inv_mul_sum_expectedHistoryValue_stageEUAt_sub
      A.phaseProfile.behaviorProfile initial who (v who) htotal_pos]
    obtain ⟨habs, -⟩ := hbounds who total htotal_pos
    rw [abs_le] at habs
    have hhigh := habs.2
    rw [hv who] at hhigh
    linarith
  · intro who dev total htotal
    obtain ⟨htotal_pos, hMerr⟩ := hstep total htotal
    rw [G.inv_mul_sum_expectedHistoryValue_stageEUAt_sub
      (Function.update A.phaseProfile.behaviorProfile who dev) initial who
      (v who) htotal_pos]
    obtain ⟨-, hdev⟩ := hbounds who total htotal_pos
    have hd := hdev dev
    rw [hv who] at hd
    linarith

/-- **Historywise handoff closure.**  Under the global criterion, the same
closed controller can be restarted at any configuration.  The rebased
response delivers that configuration's complete target and caps every
unilateral behavior deviation at every positive accuracy. -/
theorem nonempty_publicResponseEnforcementLedgerAt_rebase
    {u : A.Config → Payoff ι} (hcrit : A.IsGlobalCredibilityCriterion u)
    (z : A.Config) {err : ℝ} (herr : 0 < err) :
    Nonempty
      (G.PublicResponseEnforcementLedgerAt
        (A.rebase z).phaseProfile (A.publicState z) (u z) err) := by
  exact (A.rebase z).nonempty_publicResponseEnforcementLedgerAt
    (hcrit.rebase A z) (u z) (fun _ => rfl) herr

/-- Packaged existential form. -/
theorem isPublicPhasePunishmentSystemAt_of_isGlobalCredibilityCriterion
    {u : A.Config → Payoff ι} (hcrit : A.IsGlobalCredibilityCriterion u)
    (v : Payoff ι) (hv : ∀ who, u A.start who = v who)
    {err : ℝ} (herr : 0 < err) :
    G.IsPublicPhasePunishmentSystemAt initial v err := by
  obtain ⟨ledger⟩ :=
    A.nonempty_publicResponseEnforcementLedgerAt hcrit v hv herr
  exact ledger.toIsPublicPhasePunishmentSystemAt

/-- The verifier's adaptive certificate follows as well. -/
theorem isAdaptivePotentialCertificateAt_of_isGlobalCredibilityCriterion
    {u : A.Config → Payoff ι} (hcrit : A.IsGlobalCredibilityCriterion u)
    (v : Payoff ι) (hv : ∀ who, u A.start who = v who)
    {err : ℝ} (herr : 0 < err) :
    G.IsAdaptivePotentialCertificateAt initial v err := by
  obtain ⟨ledger⟩ :=
    A.nonempty_publicResponseEnforcementLedgerAt hcrit v hv herr
  exact ledger.toIsAdaptivePotentialCertificateAt

end HistoryBounds

end FiniteResponseArchitecture

-- ---------------------------------------------------------------------------
-- Falsifier probes
-- ---------------------------------------------------------------------------

/-!
### Falsifier probes

The one-state example of `PublicResponseCredibilityBoundary` has a feasible
target attained by a public stationary profile and a centered public
detector with strict positive drift under a pure response, yet admits *no*
enforcement ledger at error `1/4`.  A criterion that certified it would be
unsound.  The probes below show that it is rejected, and rejected for
exactly the right reason: (T0), (Ti) and (P) all hold there, and (N) fails.

The same two-configuration architecture refutes each of the other three
conditions under a different target, so no condition is vacuously true; and
with the responsive prescribed row the whole bundle is satisfied and the
criterion delivers a ledger.
-/

namespace CredibilityCriterionProbe

open ActionDetectorNoAutomaticCloser
open CredibleResponseNoAutomaticCertificate

/-- A two-configuration architecture over the one-state detector example.
The configuration records the last public action; the prescribed row is the
constant `row`. -/
def stationaryArchitecture (row : Bool) :
    game.FiniteResponseArchitecture () where
  Config := Bool
  start := false
  publicState := fun _ => ()
  play := fun _ _ => PMF.pure row
  step := fun _ act _ => act ()
  start_publicState := rfl
  step_publicState := fun _ _ _ => rfl

theorem update_play (row act : Bool) :
    Function.update (fun _ : Player => PMF.pure row) () (PMF.pure act) =
      fun _ : Player => PMF.pure act := by
  funext i
  cases i
  simp

theorem actionDist_eq (row z act : Bool) :
    (stationaryArchitecture row).actionDist () z (PMF.pure act) =
      PMF.pure (α := game.JointAct) (fun _ => act) := by
  change Math.PMFProduct.pmfPi
      (Function.update (fun _ : Player => PMF.pure row) () (PMF.pure act)) =
    PMF.pure (α := game.JointAct) (fun _ => act)
  rw [update_play]
  exact Math.PMFProduct.pmfPi_pure (fun _ : Player => act)

theorem nextConfigDist_eq (row z act : Bool) :
    (stationaryArchitecture row).nextConfigDist () z (PMF.pure act) =
      PMF.pure (α := (stationaryArchitecture row).Config) act := by
  unfold StochasticGame.FiniteResponseArchitecture.nextConfigDist
  rw [actionDist_eq]
  simp [game, stationaryArchitecture]

theorem prescribedConfigDist_eq (row z : Bool) :
    (stationaryArchitecture row).prescribedConfigDist z =
      PMF.pure (α := (stationaryArchitecture row).Config) row := by
  rw [(stationaryArchitecture row).prescribedConfigDist_eq () z]
  exact nextConfigDist_eq row z row

theorem stagePayoffAt_eq (row z act : Bool) :
    (stationaryArchitecture row).stagePayoffAt () z (PMF.pure act) =
      if act then 1 else 0 := by
  unfold StochasticGame.FiniteResponseArchitecture.stagePayoffAt
  rw [actionDist_eq, expect_pure]
  simp [game, stationaryArchitecture]

theorem prescribedStagePayoff_eq (row z : Bool) :
    (stationaryArchitecture row).prescribedStagePayoff z () =
      if row then 1 else 0 := by
  rw [(stationaryArchitecture row).prescribedStagePayoff_eq () z]
  exact stagePayoffAt_eq row z row

/-- The constant target. -/
def constTarget (c : ℝ) : Bool → Payoff Player := fun _ _ => c

/-- A configuration-dependent target: one unit after a `true` action. -/
def flagTarget : Bool → Payoff Player := fun z _ => if z then 1 else 0

/-- Occupation mass concentrated on the recurrent response pair. -/
def responseMass : Bool × Bool → ℝ := fun p => if p = (true, true) then 1 else 0

/-- Prescribed stationary mass of the obedient architecture. -/
def obeyStationaryMass : Bool → ℝ := fun z => if z then 0 else 1

theorem sum_bool_prod (f : Bool × Bool → ℝ) :
    ∑ p : Bool × Bool, f p =
      f (true, true) + f (true, false) + (f (false, true) + f (false, false)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool]

/-- A point mass gives zero real weight away from its atom. -/
theorem targetCharge_constTarget (row : Bool) (c : ℝ) (z act : Bool) :
    (stationaryArchitecture row).targetCharge (constTarget c) () z act = 0 := by
  simp [StochasticGame.FiniteResponseArchitecture.targetCharge, constTarget]

theorem isPrescribedTargetHarmonic_constTarget (row : Bool) (c : ℝ) :
    (stationaryArchitecture row).IsPrescribedTargetHarmonic
      (constTarget c) := by
  intro who z
  simp [constTarget]

theorem isUnilateralTargetSuperharmonic_constTarget (row : Bool) (c : ℝ) :
    (stationaryArchitecture row).IsUnilateralTargetSuperharmonic
      (constTarget c) := by
  intro who z act
  simp [constTarget]

/-- The prescribed profile implemented by the obedient architecture is the
in-tree `obeyProfile`. -/
theorem phaseProfile_behaviorProfile_obey :
    (stationaryArchitecture false).phaseProfile.behaviorProfile =
      obeyProfile := by
  funext i t h
  rfl

/-- The obedient architecture's zero target is the in-tree feasible
target. -/
theorem constTarget_zero_eq_feasibleTarget (z : Bool) :
    constTarget 0 z = feasibleTarget := rfl

/-- **(P) holds** on the boundary example with its feasible target. -/
theorem isPrescribedDelivery_obey :
    (stationaryArchitecture false).IsPrescribedDelivery (constTarget 0) := by
  intro who ν
  have hwho : who = () := Subsingleton.elim _ _
  subst hwho
  refine le_of_eq (Finset.sum_eq_zero fun z _ => ?_).symm
  rw [prescribedStagePayoff_eq]
  simp [constTarget]

/-- **(N) fails** on the boundary example: the response `true` is a
target-neutral unilateral occupation with strictly positive actual payoff
surplus. -/
theorem not_isNeutralOccupationNonpositive_obey :
    ¬ (stationaryArchitecture false).IsNeutralOccupationNonpositive
      (constTarget 0) := by
  intro hN
  have hle : (∑ p : Bool × Bool, responseMass p *
      ((stationaryArchitecture false).stagePayoffAt () p.1 (PMF.pure p.2) -
        constTarget 0 p.1 ())) ≤ 0 :=
    hN ()
    { mass := responseMass
      mass_nonneg := by
        intro p
        rcases eq_or_ne p (true, true) with hp | hp
        · rw [show responseMass p = 1 from if_pos hp]
          norm_num
        · rw [show responseMass p = 0 from if_neg hp]
      neutral_support := by
        intro p _
        exact targetCharge_constTarget false 0 p.1 p.2
      balance := by
        intro y
        refine Finset.sum_eq_zero fun p _ => ?_
        rcases eq_or_ne p (true, true) with hp | hp
        · rw [hp, show responseMass ((true, true) :
            (stationaryArchitecture false).Config × game.Act ()) = 1 from
              if_pos rfl, one_mul, nextConfigDist_eq]
          rcases eq_or_ne y (true : Bool) with hy | hy
          · rw [hy]
            norm_num
          · rw [if_neg hy, Math.Probability.pure_apply_toReal_of_ne _ _ hy,
              sub_zero]
        · rw [show responseMass p = 0 from if_neg hp, zero_mul]
      total := by
        change ∑ p : Bool × Bool, responseMass p = 1
        rw [sum_bool_prod]
        norm_num [responseMass] }
  rw [sum_bool_prod] at hle
  simp only [stagePayoffAt_eq, responseMass, constTarget] at hle
  norm_num at hle

/-- The exact placement of the boundary counterexample: it satisfies (T0),
(Ti) and (P), and violates only (N). -/
theorem boundary_example_fails_only_neutralOccupation :
    (stationaryArchitecture false).IsPrescribedTargetHarmonic
        (constTarget 0) ∧
      (stationaryArchitecture false).IsUnilateralTargetSuperharmonic
        (constTarget 0) ∧
      (stationaryArchitecture false).IsPrescribedDelivery (constTarget 0) ∧
      ¬ (stationaryArchitecture false).IsNeutralOccupationNonpositive
        (constTarget 0) :=
  ⟨isPrescribedTargetHarmonic_constTarget false 0,
    isUnilateralTargetSuperharmonic_constTarget false 0,
    isPrescribedDelivery_obey, not_isNeutralOccupationNonpositive_obey⟩

/-- **(P) fails** when the obedient architecture declares target one. -/
theorem not_isPrescribedDelivery_obey_one :
    ¬ (stationaryArchitecture false).IsPrescribedDelivery
      (constTarget 1) := by
  intro hP
  have h : (0 : ℝ) ≤ ∑ z : Bool, obeyStationaryMass z *
      ((stationaryArchitecture false).prescribedStagePayoff z () -
        constTarget 1 z ()) :=
    hP ()
    { mass := obeyStationaryMass
      mass_nonneg := by
        intro z
        rcases eq_or_ne z (true : Bool) with hz | hz
        · rw [show obeyStationaryMass z = 0 from if_pos hz]
        · rw [show obeyStationaryMass z = 1 from if_neg hz]
          norm_num
      balance := by
        intro y
        refine Finset.sum_eq_zero fun z _ => ?_
        rcases eq_or_ne z (true : Bool) with hz | hz
        · rw [show obeyStationaryMass z = 0 from if_pos hz, zero_mul]
        · rw [show obeyStationaryMass z = 1 from if_neg hz, one_mul]
          have hz' : z = false := by
            rcases eq_or_ne z (false : Bool) with h' | h'
            · exact h'
            · exact absurd (by cases z <;> simp_all) hz
          rw [hz', prescribedConfigDist_eq]
          rcases eq_or_ne y (false : Bool) with hy | hy
          · rw [hy]
            norm_num
          · rw [if_neg hy, Math.Probability.pure_apply_toReal_of_ne _ _ hy,
              sub_zero]
      total := by
        change ∑ z : Bool, obeyStationaryMass z = 1
        norm_num [obeyStationaryMass, Fintype.sum_bool] }
  simp only [prescribedStagePayoff_eq, obeyStationaryMass, constTarget,
    Fintype.sum_bool] at h
  norm_num at h

/-- **(T0) fails** for a configuration-dependent target. -/
theorem not_isPrescribedTargetHarmonic_flag :
    ¬ (stationaryArchitecture false).IsPrescribedTargetHarmonic flagTarget := by
  intro hT0
  have h := hT0 () true
  rw [prescribedConfigDist_eq, expect_pure] at h
  norm_num [flagTarget] at h

/-- **(Ti) fails** for a configuration-dependent target. -/
theorem not_isUnilateralTargetSuperharmonic_flag :
    ¬ (stationaryArchitecture false).IsUnilateralTargetSuperharmonic
      flagTarget := by
  intro hTi
  have h := hTi () false true
  rw [nextConfigDist_eq, expect_pure] at h
  norm_num [flagTarget] at h

/-- **(N) holds** for the responsive architecture with target one. -/
theorem isNeutralOccupationNonpositive_respond :
    (stationaryArchitecture true).IsNeutralOccupationNonpositive
      (constTarget 1) := by
  intro who μ
  have hwho : who = () := Subsingleton.elim _ _
  subst hwho
  refine Finset.sum_nonpos fun p _ => ?_
  refine mul_nonpos_of_nonneg_of_nonpos (μ.mass_nonneg p) ?_
  rw [stagePayoffAt_eq]
  by_cases hp : p.2 = true <;> simp [hp, constTarget]

/-- **(P) holds** for the responsive architecture with target one. -/
theorem isPrescribedDelivery_respond :
    (stationaryArchitecture true).IsPrescribedDelivery (constTarget 1) := by
  intro who ν
  have hwho : who = () := Subsingleton.elim _ _
  subst hwho
  refine le_of_eq (Finset.sum_eq_zero fun z _ => ?_).symm
  rw [prescribedStagePayoff_eq]
  simp [constTarget]

/-- The whole bundle is satisfiable: the responsive architecture with
target one meets (T0), (Ti), (N) and (P). -/
theorem isGlobalCredibilityCriterion_respond :
    (stationaryArchitecture true).IsGlobalCredibilityCriterion (constTarget 1) :=
  { targetHarmonic := isPrescribedTargetHarmonic_constTarget true 1
    targetSuperharmonic := isUnilateralTargetSuperharmonic_constTarget true 1
    neutralOccupation := isNeutralOccupationNonpositive_respond
    prescribedDelivery := isPrescribedDelivery_respond }

/-- Non-vacuity of the criterion direction: on the same one-state example
the criterion is met by the responsive architecture and does deliver an
enforcement ledger, at every positive error. -/
theorem nonempty_ledger_respond {err : ℝ} (herr : 0 < err) :
    Nonempty
      (game.PublicResponseEnforcementLedgerAt
        (stationaryArchitecture true).phaseProfile () (fun _ => 1) err) :=
  (stationaryArchitecture true).nonempty_publicResponseEnforcementLedgerAt
    isGlobalCredibilityCriterion_respond (fun _ => 1) (fun _ => rfl) herr

end CredibilityCriterionProbe

/-!
### Nonconstant-target and rebasing probe

The detector probe above deliberately uses a constant target.  The following
two-state absorbing game checks the other essential feature of the criterion:
the complete target may depend on the public configuration, and the global
criterion can be handed off at a configuration whose target differs from the
root target.
-/

namespace CredibilityCriterionRebaseProbe

abbrev Player := Unit
abbrev State := Bool
abbrev Action := Unit

/-- Two absorbing public states, with stage payoff equal to the state bit. -/
abbrev game : StochasticGame Player where
  State := State
  Act := fun _ => Action
  stagePayoff := fun state _ _ => if state then 1 else 0
  transition := fun state _ => PMF.pure state
  discount := 0
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

instance : Fintype game.State := inferInstanceAs (Fintype State)
instance : DecidableEq game.State := inferInstanceAs (DecidableEq State)
instance (who : Player) : Fintype (game.Act who) :=
  inferInstanceAs (Fintype Action)
instance (who : Player) : DecidableEq (game.Act who) :=
  inferInstanceAs (DecidableEq Action)

/-- The public configuration is the absorbing state itself. -/
abbrev architecture : game.FiniteResponseArchitecture false where
  Config := State
  start := false
  publicState := id
  play := fun _ _ => PMF.pure ()
  step := fun _ _ state => state
  start_publicState := rfl
  step_publicState := by intros; rfl

/-- Configuration-dependent complete target: zero at `false`, one at `true`. -/
def target : State → Payoff Player := fun state _ => if state then 1 else 0

theorem actionDist_eq (who : Player) (state : State)
    (mixed : PMF (game.Act who)) :
    architecture.actionDist who state mixed =
      PMF.pure (fun _ : Player => ()) := by
  have hmixed : mixed = PMF.pure () :=
    Math.ProbabilityMassFunction.eq_pure_of_subsingleton mixed ()
  subst mixed
  change pmfPi (fun _ : Player => PMF.pure ()) = PMF.pure (fun _ => ())
  exact Math.PMFProduct.pmfPi_pure _

theorem nextConfigDist_eq (who : Player) (state : State)
    (mixed : PMF (game.Act who)) :
    architecture.nextConfigDist who state mixed = PMF.pure state := by
  unfold StochasticGame.FiniteResponseArchitecture.nextConfigDist
  rw [actionDist_eq]
  simp [game, architecture]

theorem prescribedConfigDist_eq (state : State) :
    architecture.prescribedConfigDist state = PMF.pure state := by
  unfold StochasticGame.FiniteResponseArchitecture.prescribedConfigDist
    StochasticGame.FiniteResponseArchitecture.prescribedActionDist
  have hplay : architecture.play state =
      fun _ : Player => PMF.pure () := rfl
  rw [hplay, Math.PMFProduct.pmfPi_pure]
  simp [architecture]

theorem stagePayoffAt_eq (who : Player) (state : State)
    (mixed : PMF (game.Act who)) :
    architecture.stagePayoffAt who state mixed = if state then 1 else 0 := by
  unfold StochasticGame.FiniteResponseArchitecture.stagePayoffAt
  rw [actionDist_eq, expect_pure]
  rfl

theorem prescribedStagePayoff_eq (state : State) (who : Player) :
    architecture.prescribedStagePayoff state who = if state then 1 else 0 := by
  unfold StochasticGame.FiniteResponseArchitecture.prescribedStagePayoff
    StochasticGame.FiniteResponseArchitecture.prescribedActionDist
  have hplay : architecture.play state =
      fun _ : Player => PMF.pure () := rfl
  rw [hplay, Math.PMFProduct.pmfPi_pure, expect_pure]
  rfl

/-- The global criterion accepts a genuinely nonconstant target. -/
theorem isGlobalCredibilityCriterion :
    architecture.IsGlobalCredibilityCriterion target := by
  refine {
    targetHarmonic := ?_
    targetSuperharmonic := ?_
    neutralOccupation := ?_
    prescribedDelivery := ?_ }
  · intro who state
    rw [prescribedConfigDist_eq, expect_pure]
  · intro who state act
    rw [nextConfigDist_eq, expect_pure]
  · intro who μ
    refine Finset.sum_nonpos fun p _ => ?_
    rw [stagePayoffAt_eq]
    simp [target]
  · intro who ν
    refine Finset.sum_nonneg fun state _ => ?_
    rw [prescribedStagePayoff_eq]
    simp [target]

/-- The handoff theorem restarts at `true` and therefore certifies target one,
not the root target zero. -/
theorem nonempty_ledger_at_true {err : ℝ} (herr : 0 < err) :
    Nonempty
      (game.PublicResponseEnforcementLedgerAt
        (architecture.rebase true).phaseProfile true (target true) err) :=
  architecture.nonempty_publicResponseEnforcementLedgerAt_rebase
    isGlobalCredibilityCriterion true herr

end CredibilityCriterionRebaseProbe

end StochasticGame
end GameTheory
