/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicResponseCredibilityCriterion

/-!
# The reachable finite credibility criterion

`PublicResponseCredibilityCriterion` proves a finite Farkas sufficient
criterion after quantifying over every configuration of a supplied
controller.  That global form is convenient for rebasing, but dead controller
states can create spurious occupation obstructions.

This file gives a support-pruned sufficient version at a declared entry.  A
`ClosedResponseRegion` records

* the configurations relevant against each unilateral deviator;
* the configurations relevant under prescribed play;
* the initial configuration and the corresponding support closure facts.

The four conditions are imposed only on those regions.  The occupation tests
remain finite and target-independent of any desired ledger.  Farkas duality
produces potentials on the ambient finite configuration space, but only their
inequalities on the relevant sources are used.  Support induction then proves
that every realized history lies in the appropriate region.

The inductive predicates `UnilateralReachable` and `PrescribedReachable`
provide the canonical least regions.  Choosing those predicates removes all
states irrelevant to play from the declared entry.  This file proves the
sound criterion-to-ledger direction; it does not claim the converse from a
uniform strategic property at every state in the union of the owner-specific
arenas.  That stronger equivalence additionally needs either recurrent-class
coverage across owners or a fifth upper-delivery obstruction on prescribed
classes outside an owner's arena.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- Support-sensitive comparison of expectations along a history law. -/
theorem expect_histDist_le_of_succ_on_support
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State)
    (f g : (t : ℕ) → G.Hist t → ℝ)
    (hzero : f 0 (G.emptyHist s₀) ≤ g 0 (G.emptyHist s₀))
    (hsucc : ∀ (t : ℕ) (h : G.Hist (t + 1)),
      h ∈ (G.histDist σ s₀ (t + 1)).support →
        f (t + 1) h ≤ g (t + 1) h)
    (t : ℕ) :
    expect (G.histDist σ s₀ t) (f t) ≤
      expect (G.histDist σ s₀ t) (g t) := by
  cases t with
  | zero => rw [G.histDist_zero]; simpa using hzero
  | succ n =>
      classical
      let μ := G.histDist σ s₀ (n + 1)
      let f' : G.Hist (n + 1) → ℝ := fun h =>
        if μ h = 0 then g (n + 1) h else f (n + 1) h
      rw [expect_congr_on_support μ (f (n + 1)) f' (by
        intro h hh
        have hne : μ h ≠ 0 := by simpa [PMF.mem_support_iff] using hh
        simp [f', hne])]
      exact expect_mono μ _ _ fun h => by
        by_cases hh : μ h = 0
        · simp [f', hh]
        · have hsupp : h ∈ μ.support := by
            simpa [PMF.mem_support_iff] using hh
          simpa [f', hh] using hsucc n h hsupp

/-- Equality form of `expect_histDist_le_of_succ_on_support`. -/
theorem expect_histDist_congr_of_succ_on_support
    [Fintype ι] [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State)
    (f g : (t : ℕ) → G.Hist t → ℝ)
    (hzero : f 0 (G.emptyHist s₀) = g 0 (G.emptyHist s₀))
    (hsucc : ∀ (t : ℕ) (h : G.Hist (t + 1)),
      h ∈ (G.histDist σ s₀ (t + 1)).support →
        f (t + 1) h = g (t + 1) h)
    (t : ℕ) :
    expect (G.histDist σ s₀ t) (f t) =
      expect (G.histDist σ s₀ t) (g t) := by
  cases t with
  | zero => rw [G.histDist_zero]; simpa using hzero
  | succ n => exact expect_congr_on_support _ _ _ (hsucc n)

namespace FiniteResponseArchitecture

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)

section Reachability

variable [Fintype ι] [DecidableEq ι]

/-- A support-closed collection of configurations relevant at the chosen
entry.  `unilateral who` may depend on the owner: other players remain on the
prescribed profile while `who` can use arbitrary behavior. -/
structure ClosedResponseRegion where
  /-- Configurations relevant against a unilateral deviation by `who`. -/
  unilateral : ι → A.Config → Prop
  /-- Configurations relevant under prescribed play. -/
  prescribed : A.Config → Prop
  /-- The entry belongs to every unilateral region. -/
  start_unilateral : ∀ who, unilateral who A.start
  /-- The entry belongs to the prescribed region. -/
  start_prescribed : prescribed A.start
  /-- Prescribed-relevant configurations are relevant for every unilateral
  comparison. -/
  prescribed_unilateral : ∀ who z, prescribed z → unilateral who z
  /-- Every pure unilateral row preserves the relevant region on its support. -/
  unilateral_closed : ∀ who z, unilateral who z → ∀ act y,
    y ∈ (A.nextConfigDist who z (PMF.pure act)).support → unilateral who y
  /-- The prescribed kernel preserves the prescribed region on its support. -/
  prescribed_closed : ∀ z, prescribed z → ∀ y,
    y ∈ (A.prescribedConfigDist z).support → prescribed y

namespace ClosedResponseRegion

variable {A} (R : A.ClosedResponseRegion)

end ClosedResponseRegion
end Reachability

section BasicMixedKernel

variable [Fintype ι] [DecidableEq ι]

namespace ClosedResponseRegion

variable {A}

/-- A mixed unilateral configuration row is the mixture of its pure rows. -/
theorem nextConfigDist_eq_bind (who : ι) (z : A.Config)
    (mixed : PMF (G.Act who)) :
    A.nextConfigDist who z mixed =
      mixed.bind fun act => A.nextConfigDist who z (PMF.pure act) := by
  unfold nextConfigDist
  rw [A.actionDist_eq_bind who z mixed, PMF.bind_bind]

end ClosedResponseRegion
end BasicMixedKernel

section Reachability

variable [Fintype ι] [DecidableEq ι]

namespace ClosedResponseRegion

variable {A} (R : A.ClosedResponseRegion)

/-- Pure-row closure implies closure under an arbitrary mixed unilateral row. -/
theorem unilateral_closed_mixed (who : ι) {z : A.Config}
    (hz : R.unilateral who z) (mixed : PMF (G.Act who)) {y : A.Config}
    (hy : y ∈ (A.nextConfigDist who z mixed).support) :
    R.unilateral who y := by
  rw [nextConfigDist_eq_bind (A := A) who z mixed,
    PMF.mem_support_bind_iff] at hy
  obtain ⟨act, -, hrow⟩ := hy
  exact R.unilateral_closed who z hz act y hrow

end ClosedResponseRegion

/-- One support edge available when `who` alone may deviate. -/
def UnilateralSupportStep (A : G.FiniteResponseArchitecture initial)
    (who : ι) (z y : A.Config) : Prop :=
  ∃ act : G.Act who,
    y ∈ (A.nextConfigDist who z (PMF.pure act)).support

/-- Least support-closed set reachable while `who` alone may deviate.  Mixed
behavior needs no extra edge: every supported mixed transition is a supported
transition of one of its pure components. -/
def UnilateralReachable (A : G.FiniteResponseArchitecture initial)
    (who : ι) (z : A.Config) : Prop :=
  Relation.ReflTransGen (A.UnilateralSupportStep who) A.start z

/-- One prescribed support edge. -/
def PrescribedSupportStep (A : G.FiniteResponseArchitecture initial)
    (z y : A.Config) : Prop :=
  y ∈ (A.prescribedConfigDist z).support

/-- Least support-closed set reachable under the prescribed controller. -/
def PrescribedReachable (A : G.FiniteResponseArchitecture initial)
    (z : A.Config) : Prop :=
  Relation.ReflTransGen A.PrescribedSupportStep A.start z

/-- Prescribed reachability is contained in every player's unilateral
reachability region. -/
theorem UnilateralReachable.of_prescribed (who : ι) {z : A.Config}
    (hz : A.PrescribedReachable z) : A.UnilateralReachable who z := by
  have hedge : A.PrescribedSupportStep ≤ A.UnilateralSupportStep who := by
    intro x y hxy
    rw [PrescribedSupportStep, A.prescribedConfigDist_eq who x,
        ClosedResponseRegion.nextConfigDist_eq_bind (A := A) who x (A.play x who),
        PMF.mem_support_bind_iff] at hxy
    obtain ⟨act, -, hrow⟩ := hxy
    exact ⟨act, hrow⟩
  exact Relation.ReflTransGen.mono hedge A.start z hz

/-- The canonical least closed response region at the architecture's start. -/
def reachableRegion : A.ClosedResponseRegion where
  unilateral := A.UnilateralReachable
  prescribed := A.PrescribedReachable
  start_unilateral := fun _ => Relation.ReflTransGen.refl
  start_prescribed := Relation.ReflTransGen.refl
  prescribed_unilateral := fun who _ hz =>
    UnilateralReachable.of_prescribed (A := A) who hz
  unilateral_closed := fun _ _ hz act _ hy =>
    Relation.ReflTransGen.tail hz ⟨act, hy⟩
  prescribed_closed := fun _ hz _ hy => Relation.ReflTransGen.tail hz hy

/-! ## Support closure along realized histories -/

end Reachability

section SupportedPublicState

variable [Fintype ι]

/-- The architecture projection agrees with the current public state on every
history in the support of a play law starting from the architecture entry. -/
theorem publicState_configAt_of_mem_support (σ : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (hh : h ∈ (G.histDist σ initial t).support) :
    A.publicState (A.configAt t h) = h.2 := by
  cases t with
  | zero =>
      have heq : h = G.emptyHist initial := by
        simpa [G.histDist_zero] using hh
      subst heq
      exact A.publicState_configAt_emptyHist
  | succ n => exact A.publicState_configAt_succ h

end SupportedPublicState

section Reachability

variable [Fintype ι] [DecidableEq ι]

/-- Under a unilateral behavior deviation, every supported history reaches a
configuration in that owner's closed region. -/
theorem configAt_unilateral_of_mem_support (R : A.ClosedResponseRegion)
    (who : ι) (dev : G.BehaviorStrategy who) :
    ∀ {t : ℕ} (h : G.Hist t),
      h ∈ (G.histDist
        (Function.update A.phaseProfile.behaviorProfile who dev)
        initial t).support → R.unilateral who (A.configAt t h) := by
  intro t
  induction t with
  | zero =>
      intro h hh
      have heq : h = G.emptyHist initial := by
        simpa [G.histDist_zero] using hh
      subst heq
      exact R.start_unilateral who
  | succ n ih =>
      intro h' hh'
      rw [G.mem_support_histDist_succ] at hh'
      obtain ⟨h, hh, act, hact, s', hs', rfl⟩ := hh'
      have hz := ih h hh
      apply R.unilateral_closed_mixed who hz (dev n h)
      rw [A.stageActionDist_update who dev h] at hact
      have hstate := A.publicState_configAt_of_mem_support
        (Function.update A.phaseProfile.behaviorProfile who dev) h hh
      rw [nextConfigDist, PMF.mem_support_bind_iff]
      refine ⟨act, hact, ?_⟩
      rw [hstate]
      rw [PMF.mem_support_bind_iff]
      exact ⟨s', hs', by simpa using A.configAt_snoc h act s'⟩

/-- Under prescribed play, every supported history reaches the prescribed
closed region. -/
theorem configAt_prescribed_of_mem_support (R : A.ClosedResponseRegion) :
    ∀ {t : ℕ} (h : G.Hist t),
      h ∈ (G.histDist A.phaseProfile.behaviorProfile initial t).support →
        R.prescribed (A.configAt t h) := by
  intro t
  induction t with
  | zero =>
      intro h hh
      have heq : h = G.emptyHist initial := by
        simpa [G.histDist_zero] using hh
      subst heq
      exact R.start_prescribed
  | succ n ih =>
      intro h' hh'
      rw [G.mem_support_histDist_succ] at hh'
      obtain ⟨h, hh, act, hact, s', hs', rfl⟩ := hh'
      have hz := ih h hh
      apply R.prescribed_closed (A.configAt n h) hz
      rw [A.stageActionDist_prescribed h] at hact
      rw [prescribedConfigDist, PMF.mem_support_bind_iff]
      refine ⟨act, hact, ?_⟩
      have hstate := A.publicState_configAt_of_mem_support
        A.phaseProfile.behaviorProfile h hh
      rw [hstate, PMF.mem_support_bind_iff]
      exact ⟨s', hs', by simpa using A.configAt_snoc h act s'⟩

end Reachability

section FiniteReachableAlgebra

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (G.Act i)]

/-! ## The four conditions on a closed reachable region -/

/-- Reachable version of (T0): target harmonicity is required only at
prescribed-relevant configurations. -/
def IsPrescribedTargetHarmonicOn (R : A.ClosedResponseRegion)
    (u : A.Config → Payoff ι) : Prop :=
  ∀ (who : ι) (z : A.Config), R.prescribed z →
    expect (A.prescribedConfigDist z) (fun y => u y who) = u z who

/-- Reachable version of (Ti): target superharmonicity is required only at
configurations that can matter against that owner. -/
def IsUnilateralTargetSuperharmonicOn (R : A.ClosedResponseRegion)
    (u : A.Config → Payoff ι) : Prop :=
  ∀ (who : ι) (z : A.Config), R.unilateral who z → ∀ act : G.Act who,
    expect (A.nextConfigDist who z (PMF.pure act)) (fun y => u y who) ≤
      u z who

/-- A normalized invariant target-neutral occupation supported inside the
unilateral region of its owner.  Balance is imposed in the ambient state
space, so no hidden no-leakage assumption is built into the definition. -/
structure NeutralOccupationOn (R : A.ClosedResponseRegion)
    (u : A.Config → Payoff ι) (who : ι) where
  mass : A.Config × G.Act who → ℝ
  mass_nonneg : ∀ p, 0 ≤ mass p
  relevant_support : ∀ p, 0 < mass p → R.unilateral who p.1
  neutral_support : ∀ p, 0 < mass p → A.targetCharge u who p.1 p.2 = 0
  balance : ∀ y : A.Config,
    ∑ p : A.Config × G.Act who,
      mass p * ((A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal -
        if y = p.1 then 1 else 0) = 0
  total : ∑ p : A.Config × G.Act who, mass p = 1

namespace NeutralOccupationOn

variable {A} {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
  {who : ι}

/-- Actual payoff surplus of a reachable neutral occupation. -/
def surplus (μ : A.NeutralOccupationOn R u who) : ℝ :=
  ∑ p : A.Config × G.Act who,
    μ.mass p * (A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who)

end NeutralOccupationOn

/-- Reachable version of (N). -/
def IsNeutralOccupationNonpositiveOn (R : A.ClosedResponseRegion)
    (u : A.Config → Payoff ι) : Prop :=
  ∀ (who : ι) (μ : A.NeutralOccupationOn R u who), μ.surplus ≤ 0

/-- A normalized prescribed stationary occupation supported in the
prescribed-relevant region. -/
structure PrescribedStationaryOn (R : A.ClosedResponseRegion) where
  mass : A.Config → ℝ
  mass_nonneg : ∀ z, 0 ≤ mass z
  relevant_support : ∀ z, 0 < mass z → R.prescribed z
  balance : ∀ y : A.Config,
    ∑ z : A.Config,
      mass z * ((A.prescribedConfigDist z y).toReal -
        if y = z then 1 else 0) = 0
  total : ∑ z : A.Config, mass z = 1

/-- Reachable version of (P). -/
def IsPrescribedDeliveryOn (R : A.ClosedResponseRegion)
    (u : A.Config → Payoff ι) : Prop :=
  ∀ (who : ι) (ν : A.PrescribedStationaryOn R),
    0 ≤ ∑ z : A.Config,
      ν.mass z * (A.prescribedStagePayoff z who - u z who)

/-- A finite sufficient criterion on a chosen closed relevant region.  No
field mentions a potential, ledger, punishment system, or payoff cap. -/
structure IsReachableCredibilityCriterion (R : A.ClosedResponseRegion)
    (u : A.Config → Payoff ι) : Prop where
  targetHarmonic : A.IsPrescribedTargetHarmonicOn R u
  targetSuperharmonic : A.IsUnilateralTargetSuperharmonicOn R u
  neutralOccupation : A.IsNeutralOccupationNonpositiveOn R u
  prescribedDelivery : A.IsPrescribedDeliveryOn R u

/-- The global criterion implies the criterion on every closed relevant
region.  Thus the reachable theorem strictly extends the earlier global
consumer rather than replacing it with an incompatible interface. -/
theorem IsGlobalCredibilityCriterion.toReachable
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hcrit : A.IsGlobalCredibilityCriterion u) :
    A.IsReachableCredibilityCriterion R u := by
  refine
    { targetHarmonic := fun who z _ => hcrit.targetHarmonic who z
      targetSuperharmonic := fun who z _ act =>
        hcrit.targetSuperharmonic who z act
      neutralOccupation := ?_
      prescribedDelivery := ?_ }
  · intro who μ
    let μ' : A.NeutralOccupation u who :=
      { mass := μ.mass
        mass_nonneg := μ.mass_nonneg
        neutral_support := μ.neutral_support
        balance := μ.balance
        total := μ.total }
    simpa [NeutralOccupationOn.surplus, NeutralOccupation.surplus] using
      hcrit.neutralOccupation who μ'
  · intro who ν
    let ν' : A.PrescribedStationary :=
      { mass := ν.mass
        mass_nonneg := ν.mass_nonneg
        balance := ν.balance
        total := ν.total }
    simpa using hcrit.prescribedDelivery who ν'

end FiniteReachableAlgebra

section BasicReachableTargetCharge

variable [Fintype ι] [DecidableEq ι]

/-! ## Farkas potentials on the relevant sources -/

/-- On a relevant source, (Ti) makes the target charge nonnegative. -/
theorem targetCharge_nonnegOn {R : A.ClosedResponseRegion}
    {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (who : ι) {z : A.Config} (hz : R.unilateral who z)
    (act : G.Act who) : 0 ≤ A.targetCharge u who z act := by
  have h := hTi who z hz act
  simp only [targetCharge]
  linarith

end BasicReachableTargetCharge

section MixedReachableTargetRows

variable [Fintype ι] [DecidableEq ι] [∀ i, Finite (G.Act i)]

/-- Mixed form of reachable (Ti). -/
theorem expect_nextConfigDist_target_le_on {R : A.ClosedResponseRegion}
    {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (who : ι) {z : A.Config} (hz : R.unilateral who z)
    (mixed : PMF (G.Act who)) :
    expect (A.nextConfigDist who z mixed) (fun y => u y who) ≤ u z who := by
  rw [A.expect_nextConfigDist_eq_expect who z mixed]
  calc
    expect mixed
        (fun act => expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => u y who)) ≤ expect mixed (fun _ => u z who) :=
      expect_mono _ _ _ fun act => hTi who z hz act
    _ = u z who := expect_const _ _

end MixedReachableTargetRows

section FiniteReachableAlgebra

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (G.Act i)]

/-- Reachable Farkas step for (N).  The resulting potential is defined on the
ambient finite configuration space, but its Bellman inequality is asserted
only at sources relevant against `who`. -/
theorem exists_deviationPotentialOn {R : A.ClosedResponseRegion}
    {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (hN : A.IsNeutralOccupationNonpositiveOn R u) (who : ι) :
    ∃ Φ : A.Config → ℝ, ∀ (z : A.Config), R.unilateral who z →
      ∀ act : G.Act who,
        A.stagePayoffAt who z (PMF.pure act) +
            expect (A.nextConfigDist who z (PMF.pure act)) Φ ≤
          u z who + Φ z := by
  classical
  letI : DecidablePred (fun p : A.Config × G.Act who =>
      R.unilateral who p.1 ∧ A.targetCharge u who p.1 p.2 = 0) :=
    Classical.decPred _
  set kernel : A.Config × G.Act who → PMF A.Config := fun p =>
    if R.unilateral who p.1 ∧ A.targetCharge u who p.1 p.2 = 0 then
      A.nextConfigDist who p.1 (PMF.pure p.2)
    else PMF.pure p.1 with hkernel
  set source : A.Config × G.Act who → A.Config := fun p => p.1 with hsource
  set charge : A.Config × G.Act who → ℝ := fun p =>
    if R.unilateral who p.1 ∧ A.targetCharge u who p.1 p.2 = 0 then
      A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who
    else 0 with hcharge
  have hoff : ∀ p : A.Config × G.Act who,
      ¬(R.unilateral who p.1 ∧ A.targetCharge u who p.1 p.2 = 0) →
        ∀ y : A.Config, actualOccupationColumn kernel source p y = 0 := by
    intro p hp y
    simp [actualOccupationColumn, hkernel, hsource, hp, PMF.pure_apply,
      apply_ite ENNReal.toReal]
  have halt :=
    normalizedPositiveChargedCirculation_xor_driftPotential kernel source charge
  rw [xor_def] at halt
  have hpotential : ∃ ξ : A.Config → ℝ, ∀ p : A.Config × G.Act who,
      charge p ≤ expect (kernel p) ξ - ξ (source p) := by
    rcases halt with ⟨hcirc, -⟩ | ⟨hpot, -⟩
    · exfalso
      obtain ⟨mass, hmass, hbalance, htotal⟩ := hcirc
      set restricted : A.Config × G.Act who → ℝ := fun p =>
        if R.unilateral who p.1 ∧ A.targetCharge u who p.1 p.2 = 0 then
          mass p
        else 0 with hrestricted
      have hrestricted_nonneg : ∀ p, 0 ≤ restricted p := by
        intro p
        by_cases hp : R.unilateral who p.1 ∧
            A.targetCharge u who p.1 p.2 = 0 <;>
          simp [hrestricted, hp, hmass p]
      have hterm : ∀ (p : A.Config × G.Act who) (y : A.Config),
          restricted p *
              ((A.nextConfigDist who p.1 (PMF.pure p.2) y).toReal -
                if y = p.1 then 1 else 0) =
            mass p * actualOccupationColumn kernel source p y := by
        intro p y
        by_cases hp : R.unilateral who p.1 ∧
            A.targetCharge u who p.1 p.2 = 0
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
            by_cases hp : R.unilateral who p.1 ∧
                A.targetCharge u who p.1 p.2 = 0
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
        { mass := fun p => restricted p /
              (∑ q : A.Config × G.Act who, restricted q)
          mass_nonneg := fun p => div_nonneg (hrestricted_nonneg p) hSpos.le
          relevant_support := by
            intro p hp
            by_contra hrel
            have hzero : restricted p = 0 := by
              rw [hrestricted]
              simp [hrel]
            rw [hzero, zero_div] at hp
            exact absurd hp (lt_irrefl 0)
          neutral_support := by
            intro p hp
            by_contra hne
            have hzero : restricted p = 0 := by
              rw [hrestricted]
              simp [hne]
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
      have hone : (0 : ℝ) < 1 /
          (∑ q : A.Config × G.Act who, restricted q) :=
        div_pos zero_lt_one hSpos
      linarith
    · exact hpot
  obtain ⟨ξ, hξ⟩ := hpotential
  have hneutral : ∀ (z : A.Config), R.unilateral who z →
      ∀ act : G.Act who, A.targetCharge u who z act = 0 →
        A.stagePayoffAt who z (PMF.pure act) - u z who ≤
          expect (A.nextConfigDist who z (PMF.pure act)) ξ - ξ z := by
    intro z hz act hzero
    have hp := hξ (z, act)
    simpa [hcharge, hkernel, hsource, hz, hzero] using hp
  set gap : A.Config × G.Act who → ℝ := fun p =>
    A.stagePayoffAt who p.1 (PMF.pure p.2) - u p.1 who -
      (expect (A.nextConfigDist who p.1 (PMF.pure p.2)) ξ - ξ p.1) with hgap
  set ratio : A.Config × G.Act who → ℝ := fun p =>
    if A.targetCharge u who p.1 p.2 = 0 then 0
    else gap p / A.targetCharge u who p.1 p.2 with hratio
  have hratio_le : ∀ p, ratio p ≤
      ∑ q : A.Config × G.Act who, |ratio q| := by
    intro p
    calc
      ratio p ≤ |ratio p| := le_abs_self _
      _ ≤ ∑ q : A.Config × G.Act who, |ratio q| :=
        Finset.single_le_sum (f := fun q => |ratio q|)
          (fun q _ => abs_nonneg _) (Finset.mem_univ p)
  have hgap_le : ∀ p : A.Config × G.Act who, R.unilateral who p.1 →
      gap p ≤ (∑ q : A.Config × G.Act who, |ratio q|) *
        A.targetCharge u who p.1 p.2 := by
    intro p hpRel
    by_cases hp : A.targetCharge u who p.1 p.2 = 0
    · have hn := hneutral p.1 hpRel p.2 hp
      rw [hp, mul_zero, hgap]
      simp only
      linarith
    · have hpos : 0 < A.targetCharge u who p.1 p.2 :=
        lt_of_le_of_ne (A.targetCharge_nonnegOn hTi who hpRel p.2) (Ne.symm hp)
      have hr : ratio p = gap p / A.targetCharge u who p.1 p.2 := by
        rw [hratio]
        simp [hp]
      have hle := hratio_le p
      rw [hr, div_le_iff₀ hpos] at hle
      exact hle
  refine ⟨fun z => (∑ q : A.Config × G.Act who, |ratio q|) * u z who - ξ z, ?_⟩
  intro z hz act
  have hgapz := hgap_le (z, act) hz
  rw [hgap] at hgapz
  simp only [targetCharge] at hgapz
  have hsplit :
      expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => (∑ q : A.Config × G.Act who, |ratio q|) * u y who - ξ y) =
        (∑ q : A.Config × G.Act who, |ratio q|) *
            expect (A.nextConfigDist who z (PMF.pure act))
              (fun y => u y who) -
          expect (A.nextConfigDist who z (PMF.pure act)) ξ := by
    rw [expect_sub, expect_const_mul]
  rw [hsplit]
  linarith

end FiniteReachableAlgebra

section PrescribedReachableAlgebra

variable [Fintype ι] [DecidableEq ι]

/-- Reachable Farkas step for (P). -/
theorem exists_deliveryPotentialOn {R : A.ClosedResponseRegion}
    {u : A.Config → Payoff ι}
    (hP : A.IsPrescribedDeliveryOn R u) (who : ι) :
    ∃ Ψ : A.Config → ℝ, ∀ z : A.Config, R.prescribed z →
      u z who + Ψ z ≤ A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) Ψ := by
  classical
  letI : DecidablePred R.prescribed := Classical.decPred _
  set kernel : A.Config → PMF A.Config := fun z =>
    if R.prescribed z then A.prescribedConfigDist z else PMF.pure z with hkernel
  set charge : A.Config → ℝ := fun z =>
    if R.prescribed z then u z who - A.prescribedStagePayoff z who else 0
    with hcharge
  have hoff : ∀ z : A.Config, ¬R.prescribed z →
      ∀ y : A.Config,
        actualOccupationColumn kernel (fun q : A.Config => q) z y = 0 := by
    intro z hz y
    simp [actualOccupationColumn, hkernel, hz, PMF.pure_apply,
      apply_ite ENNReal.toReal]
  have halt := normalizedPositiveChargedCirculation_xor_driftPotential
    kernel (fun z : A.Config => z) charge
  rw [xor_def] at halt
  rcases halt with ⟨hcirc, -⟩ | ⟨hpot, -⟩
  · exfalso
    obtain ⟨mass, hmass, hbalance, htotal⟩ := hcirc
    set restricted : A.Config → ℝ := fun z =>
      if R.prescribed z then mass z else 0 with hrestricted
    have hrestricted_nonneg : ∀ z, 0 ≤ restricted z := by
      intro z
      by_cases hz : R.prescribed z <;> simp [hrestricted, hz, hmass z]
    have hterm : ∀ (z y : A.Config),
        restricted z * ((A.prescribedConfigDist z y).toReal -
            if y = z then 1 else 0) =
          mass z * actualOccupationColumn kernel (fun q : A.Config => q) z y := by
      intro z y
      by_cases hz : R.prescribed z
      · simp [hrestricted, hz, actualOccupationColumn, hkernel]
      · simp [hrestricted, hz, hoff z hz y]
    have hbalance' : ∀ y : A.Config,
        ∑ z : A.Config, restricted z *
          ((A.prescribedConfigDist z y).toReal -
            if y = z then 1 else 0) = 0 := by
      intro y
      rw [Finset.sum_congr rfl fun z _ => hterm z y]
      exact hbalance y
    have hchargeSum :
        ∑ z : A.Config, restricted z *
          (u z who - A.prescribedStagePayoff z who) = 1 := by
      rw [Finset.sum_congr rfl fun z (_ : z ∈ Finset.univ) =>
        show restricted z * (u z who - A.prescribedStagePayoff z who) =
          mass z * charge z by
          by_cases hz : R.prescribed z
          · simp [hrestricted, hcharge, hz]
          · simp [hrestricted, hcharge, hz]]
      exact htotal
    have hSnonneg : 0 ≤ ∑ z : A.Config, restricted z :=
      Finset.sum_nonneg fun z _ => hrestricted_nonneg z
    have hSpos : 0 < ∑ z : A.Config, restricted z := by
      rcases hSnonneg.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hzero : ∀ z : A.Config, restricted z = 0 := fun z =>
          (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hrestricted_nonneg q).1
            heq.symm z (Finset.mem_univ z)
        have hz : ∑ z : A.Config, restricted z *
            (u z who - A.prescribedStagePayoff z who) = 0 :=
          Finset.sum_eq_zero fun z _ => by rw [hzero z]; ring
        linarith
    have hdelivery : 0 ≤ ∑ z : A.Config,
        restricted z / (∑ y : A.Config, restricted y) *
          (A.prescribedStagePayoff z who - u z who) :=
      hP who
      { mass := fun z => restricted z / (∑ y : A.Config, restricted y)
        mass_nonneg := fun z => div_nonneg (hrestricted_nonneg z) hSpos.le
        relevant_support := by
          intro z hz
          by_contra hrel
          have hzero : restricted z = 0 := by rw [hrestricted]; simp [hrel]
          rw [hzero, zero_div] at hz
          exact absurd hz (lt_irrefl 0)
        balance := by
          intro y
          have hb := hbalance' y
          calc
            ∑ z : A.Config, restricted z / (∑ w : A.Config, restricted w) *
                ((A.prescribedConfigDist z y).toReal -
                  if y = z then 1 else 0) =
                (∑ z : A.Config, restricted z *
                  ((A.prescribedConfigDist z y).toReal -
                    if y = z then 1 else 0)) /
                  (∑ w : A.Config, restricted w) := by
                    rw [Finset.sum_div]
                    exact Finset.sum_congr rfl fun z _ => by ring
            _ = 0 := by rw [hb, zero_div]
        total := by
          rw [← Finset.sum_div]
          exact div_self (ne_of_gt hSpos) }
    have hcalc : (∑ z : A.Config,
        restricted z / (∑ w : A.Config, restricted w) *
          (A.prescribedStagePayoff z who - u z who)) =
        -((∑ z : A.Config, restricted z *
          (u z who - A.prescribedStagePayoff z who)) /
            (∑ w : A.Config, restricted w)) := by
      rw [← neg_div, ← Finset.sum_neg_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [hcalc, hchargeSum] at hdelivery
    have hone : (0 : ℝ) < 1 / (∑ w : A.Config, restricted w) :=
      div_pos zero_lt_one hSpos
    linarith
  · obtain ⟨Ψ, hΨ⟩ := hpot
    refine ⟨Ψ, fun z hz => ?_⟩
    have hrow := hΨ z
    simp [hkernel, hcharge, hz] at hrow
    linarith

end PrescribedReachableAlgebra

section ReachablePathBounds

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-! ## Realized target processes -/

/-- Reachable (Ti) makes the realized target a supermartingale against every
unilateral behavior deviation. -/
theorem expectedTarget_update_le_on {R : A.ClosedResponseRegion}
    {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u)
    (who : ι) (dev : G.BehaviorStrategy who) (t : ℕ) :
    G.expectedHistoryValue
        (Function.update A.phaseProfile.behaviorProfile who dev) initial
        (fun t h => u (A.configAt t h) who) t ≤ u A.start who := by
  induction t with
  | zero => simp [expectedHistoryValue]
  | succ n ih =>
      refine le_trans ?_ ih
      rw [G.expectedHistoryValue_succ]
      refine expect_histDist_le_of_succ_on_support _ initial
        (fun t h => G.historyContinuationEU
          (Function.update A.phaseProfile.behaviorProfile who dev)
          (fun t h => u (A.configAt t h) who) h)
        (fun t h => u (A.configAt t h) who) ?_ ?_ n
      · rw [A.historyContinuationEU_update who dev (fun y => u y who) _
          A.publicState_configAt_emptyHist]
        exact A.expect_nextConfigDist_target_le_on hTi who
          (R.start_unilateral who) _
      · intro m h hh
        rw [A.historyContinuationEU_update who dev (fun y => u y who) h
          (A.publicState_configAt_succ h)]
        exact A.expect_nextConfigDist_target_le_on hTi who
          (A.configAt_unilateral_of_mem_support R who dev h hh) _

/-- Reachable (T0) makes the realized target a martingale under prescribed
play. -/
theorem expectedTarget_prescribed_eq_on {R : A.ClosedResponseRegion}
    {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u) (who : ι) (t : ℕ) :
    G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
        (fun t h => u (A.configAt t h) who) t = u A.start who := by
  induction t with
  | zero => simp [expectedHistoryValue]
  | succ n ih =>
      rw [← ih, G.expectedHistoryValue_succ]
      refine expect_histDist_congr_of_succ_on_support _ initial
        (fun t h => G.historyContinuationEU A.phaseProfile.behaviorProfile
          (fun t h => u (A.configAt t h) who) h)
        (fun t h => u (A.configAt t h) who) ?_ ?_ n
      · rw [A.historyContinuationEU_prescribed (fun y => u y who) _
          A.publicState_configAt_emptyHist]
        exact hT0 who _ R.start_prescribed
      · intro m h hh
        rw [A.historyContinuationEU_prescribed (fun y => u y who) h
          (A.publicState_configAt_succ h)]
        exact hT0 who _ (A.configAt_prescribed_of_mem_support R h hh)

/-! ## Reachable payoff bounds -/

/-- A deviation potential valid on the unilateral region caps every actual
behavior deviation with the same `O(1/T)` endpoint remainder as in the global
criterion. -/
theorem finiteAveragePayoff_update_le_on {R : A.ClosedResponseRegion}
    {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u) (who : ι)
    (Φ : A.Config → ℝ)
    (hΦ : ∀ (z : A.Config), R.unilateral who z → ∀ act : G.Act who,
      A.stagePayoffAt who z (PMF.pure act) +
          expect (A.nextConfigDist who z (PMF.pure act)) Φ ≤ u z who + Φ z)
    (dev : G.BehaviorStrategy who) {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff initial T
        (Function.update A.phaseProfile.behaviorProfile who dev) who ≤
      u A.start who + 2 * A.configBound Φ / T := by
  have hΦmix : ∀ (z : A.Config), R.unilateral who z →
      ∀ mixed : PMF (G.Act who),
        A.stagePayoffAt who z mixed +
            expect (A.nextConfigDist who z mixed) Φ ≤ u z who + Φ z := by
    intro z hz mixed
    rw [A.stagePayoffAt_eq_expect who z mixed,
      A.expect_nextConfigDist_eq_expect who z mixed Φ, ← expect_add]
    calc
      expect mixed (fun act => A.stagePayoffAt who z (PMF.pure act) +
          expect (A.nextConfigDist who z (PMF.pure act)) Φ) ≤
          expect mixed (fun _ => u z who + Φ z) :=
        expect_mono _ _ _ fun act => hΦ z hz act
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
    refine expect_histDist_le_of_succ_on_support _ initial
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
      exact hΦmix _ (R.start_unilateral who) _
    · intro m h hh
      rw [A.stageEUAt_update who dev _ (A.publicState_configAt_succ h),
        A.historyContinuationEU_update who dev _ _
          (A.publicState_configAt_succ h)]
      exact hΦmix _ (A.configAt_unilateral_of_mem_support R who dev h hh) _
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
        Finset.sum_le_sum fun t _ =>
          A.expectedTarget_update_le_on hTi who dev t
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

/-- Prescribed play is the special unilateral behavior that keeps the
prescribed row, so the reachable deviation potential also supplies its upper
bound. -/
theorem finiteAveragePayoff_prescribed_le_on {R : A.ClosedResponseRegion}
    {u : A.Config → Payoff ι}
    (hTi : A.IsUnilateralTargetSuperharmonicOn R u) (who : ι)
    (Φ : A.Config → ℝ)
    (hΦ : ∀ (z : A.Config), R.unilateral who z → ∀ act : G.Act who,
      A.stagePayoffAt who z (PMF.pure act) +
          expect (A.nextConfigDist who z (PMF.pure act)) Φ ≤ u z who + Φ z)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff initial T A.phaseProfile.behaviorProfile who ≤
      u A.start who + 2 * A.configBound Φ / T := by
  have h := A.finiteAveragePayoff_update_le_on hTi who Φ hΦ
    (A.phaseProfile.behaviorProfile who) hT
  rwa [Function.update_eq_self] at h

/-- A delivery potential valid on the prescribed region supplies the matching
lower bound under prescribed play. -/
theorem le_finiteAveragePayoff_prescribed_on {R : A.ClosedResponseRegion}
    {u : A.Config → Payoff ι}
    (hT0 : A.IsPrescribedTargetHarmonicOn R u)
    (who : ι) (Ψ : A.Config → ℝ)
    (hΨ : ∀ z : A.Config, R.prescribed z →
      u z who + Ψ z ≤ A.prescribedStagePayoff z who +
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
    refine expect_histDist_le_of_succ_on_support _ initial
      (fun t h => u (A.configAt t h) who + Ψ (A.configAt t h))
      (fun t h =>
        G.stageEUAt A.phaseProfile.behaviorProfile h who +
          G.historyContinuationEU A.phaseProfile.behaviorProfile
            (fun t h => Ψ (A.configAt t h)) h) ?_ ?_ t
    · rw [A.stageEUAt_prescribed who _ A.publicState_configAt_emptyHist,
        A.historyContinuationEU_prescribed _ _
          A.publicState_configAt_emptyHist]
      exact hΨ _ R.start_prescribed
    · intro m h hh
      rw [A.stageEUAt_prescribed who _ (A.publicState_configAt_succ h),
        A.historyContinuationEU_prescribed _ _
          (A.publicState_configAt_succ h)]
      exact hΨ _ (A.configAt_prescribed_of_mem_support R h hh)
  have htel := sumStep_telescope_ge hstep T
  have hsumU :
      (∑ t ∈ Finset.range T,
          G.expectedHistoryValue A.phaseProfile.behaviorProfile initial
            (fun t h => u (A.configAt t h) who) t) =
        (T : ℝ) * u A.start who := by
    rw [Finset.sum_congr rfl fun t _ =>
      A.expectedTarget_prescribed_eq_on hT0 who t]
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

end ReachablePathBounds

section ReachableCriterionConsumers

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Fintype (G.Act i)]

/-! ## The support-pruned criterion direction -/

/-- The reachable four-condition criterion produces one explicit modulus for
prescribed delivery and all unilateral deviations. -/
theorem exists_uniformModulus_of_isReachableCredibilityCriterion
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hcrit : A.IsReachableCredibilityCriterion R u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (who : ι) (T : ℕ), 0 < T →
      |G.finiteAveragePayoff initial T A.phaseProfile.behaviorProfile who -
          u A.start who| ≤ M / T ∧
        ∀ dev : G.BehaviorStrategy who,
          G.finiteAveragePayoff initial T
              (Function.update A.phaseProfile.behaviorProfile who dev)
              who ≤ u A.start who + M / T := by
  classical
  choose Φ hΦ using fun who =>
    A.exists_deviationPotentialOn hcrit.targetSuperharmonic
      hcrit.neutralOccupation who
  choose Ψ hΨ using fun who =>
    A.exists_deliveryPotentialOn hcrit.prescribedDelivery who
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
  have hupper := A.finiteAveragePayoff_prescribed_le_on
    hcrit.targetSuperharmonic who (Φ who) (hΦ who) hT
  have hlower := A.le_finiteAveragePayoff_prescribed_on
    hcrit.targetHarmonic who (Ψ who) (hΨ who) hT
  refine ⟨?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith
  · intro dev
    have hdev := A.finiteAveragePayoff_update_le_on
      hcrit.targetSuperharmonic who (Φ who) (hΦ who) dev hT
    linarith

/-- **Support-pruned criterion direction.**  Dead configurations are absent
from every hypothesis, yet the conclusion is the same operational ledger
consumed by the public-response compilers. -/
theorem nonempty_publicResponseEnforcementLedgerAt_of_reachable
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hcrit : A.IsReachableCredibilityCriterion R u)
    (v : Payoff ι) (hv : ∀ who, u A.start who = v who)
    {err : ℝ} (herr : 0 < err) :
    Nonempty
      (G.PublicResponseEnforcementLedgerAt A.phaseProfile initial v err) := by
  classical
  obtain ⟨M, hM, hbounds⟩ :=
    A.exists_uniformModulus_of_isReachableCredibilityCriterion hcrit
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

/-- The reachable criterion yields the punishment-system interface. -/
theorem isPublicPhasePunishmentSystemAt_of_isReachableCredibilityCriterion
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hcrit : A.IsReachableCredibilityCriterion R u)
    (v : Payoff ι) (hv : ∀ who, u A.start who = v who)
    {err : ℝ} (herr : 0 < err) :
    G.IsPublicPhasePunishmentSystemAt initial v err := by
  obtain ⟨ledger⟩ :=
    A.nonempty_publicResponseEnforcementLedgerAt_of_reachable
      hcrit v hv herr
  exact ledger.toIsPublicPhasePunishmentSystemAt

/-- The verifier's adaptive certificate follows from the support-pruned
criterion. -/
theorem isAdaptivePotentialCertificateAt_of_isReachableCredibilityCriterion
    {R : A.ClosedResponseRegion} {u : A.Config → Payoff ι}
    (hcrit : A.IsReachableCredibilityCriterion R u)
    (v : Payoff ι) (hv : ∀ who, u A.start who = v who)
    {err : ℝ} (herr : 0 < err) :
    G.IsAdaptivePotentialCertificateAt initial v err := by
  obtain ⟨ledger⟩ :=
    A.nonempty_publicResponseEnforcementLedgerAt_of_reachable
      hcrit v hv herr
  exact ledger.toIsAdaptivePotentialCertificateAt

end ReachableCriterionConsumers

end FiniteResponseArchitecture
end StochasticGame
end GameTheory
