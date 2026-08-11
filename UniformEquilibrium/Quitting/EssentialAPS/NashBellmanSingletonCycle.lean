/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Cycle
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium
import UniformEquilibrium.Quitting.Terminal.TargetTail.InfiniteSingletonMeshCertificate

/-!
# Singleton Nash--Bellman cycles as essential-APS cycles

Physical Nash--Bellman edges and essential-APS segments use different input
languages.  A Nash--Bellman edge carries a product root and exact one-stage
Nash conditions, while an essential-APS segment names its active singleton
owner, its absorption mass, and the affine continuation equation.

On the singleton-root stratum these languages agree.  A positive proper
singleton root turns the Bellman policy equation into the singleton-arc
equation, and exact mixing pins the current owner's coordinate to its solo
reward.  Consequently a finite state-matched cyclic word of such physical
edges, with viable displayed values and changing owners, is already an
executable essential-APS cycle.

The capstone compiles the word to a uniform-equilibrium payoff.  In
particular, no additional cycle-punishment field is needed on this stratum:
owner changes give every player a strictly contracting opponent factor, and
the singleton mesh makes collision errors vanish.  This is specific to
singleton roots; general product-root returns still require collision-aware
strategic control.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The policy equation of a physical singleton-root edge is the
singleton-arc equation. -/
theorem IsQuittingNashBellmanEdge.eq_singletonArc_of_root
    {current tail : QuittingNashBellmanPoint ι}
    (edge : IsQuittingNashBellmanEdge reward current tail)
    (owner : ι) {mass : ℝ} (hmass0 : 0 ≤ mass) (hmass1 : mass ≤ 1)
    (hroot : quittingRootOfSimplex current.2 =
      quittingSoloStationaryRoot owner
        (quittingHazardCoin mass hmass0 hmass1)) :
    current.1 = quittingSingletonArcPayoff mass
      (quittingSoloReward reward owner) tail.1 := by
  rw [edge.1, hroot, quittingRootSuccessorPayoff_solo]
  funext who
  simp [quittingSingletonArcPayoff]

/-- Exact mixing at a proper physical singleton root pins the current owner
to its solo payoff. -/
theorem IsQuittingNashBellmanEdge.active_eq_solo_of_singleton
    {current tail : QuittingNashBellmanPoint ι}
    (edge : IsQuittingNashBellmanEdge reward current tail)
    (owner : ι) {mass : ℝ} (hmassPos : 0 < mass) (hmassLt : mass < 1)
    (hroot : quittingRootOfSimplex current.2 =
      quittingSoloStationaryRoot owner
        (quittingHazardCoin mass hmassPos.le hmassLt.le)) :
    current.1 owner = quittingSoloReward reward owner owner := by
  have hquitProbability :
      ((quittingRootOfSimplex current.2) owner true).toReal = mass := by
    rw [hroot]
    simp [quittingSoloStationaryRoot]
  have hcontinueProbability :
      ((quittingRootOfSimplex current.2) owner false).toReal = 1 - mass := by
    rw [hroot]
    simp [quittingSoloStationaryRoot]
  have hdifference : quittingRootEndpointDifference reward tail.1
      (quittingRootOfSimplex current.2) owner = 0 :=
    quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
      reward tail.1 (quittingRootOfSimplex current.2) owner edge.2
        (by rw [hcontinueProbability]; linarith)
        (by rw [hquitProbability]; exact hmassPos)
  have hendpoints : quittingRootQuitPayoff reward tail.1
        (quittingRootOfSimplex current.2) owner =
      quittingRootContinuePayoff reward tail.1
        (quittingRootOfSimplex current.2) owner := by
    exact sub_eq_zero.mp hdifference
  calc
    current.1 owner = quittingRootSuccessorPayoff reward tail.1
        (quittingRootOfSimplex current.2) owner := congrFun edge.1 owner
    _ = ((quittingRootOfSimplex current.2) owner true).toReal *
          quittingRootQuitPayoff reward tail.1
            (quittingRootOfSimplex current.2) owner +
        ((quittingRootOfSimplex current.2) owner false).toReal *
          quittingRootContinuePayoff reward tail.1
            (quittingRootOfSimplex current.2) owner :=
      quittingRootSuccessorPayoff_eq_endpointMix reward tail.1
        (quittingRootOfSimplex current.2) owner
    _ = quittingRootQuitPayoff reward tail.1
          (quittingRootOfSimplex current.2) owner := by
      rw [hquitProbability, hcontinueProbability, hendpoints]
      ring
    _ = quittingSoloReward reward owner owner := by
      rw [hroot, quittingRootQuitPayoff_soloStationaryRoot_owner]

/-- One exact Nash--Bellman edge whose current product root is a proper
singleton root is exactly a proper essential-APS segment. -/
theorem IsQuittingNashBellmanEdge.mem_quittingProperEssentialAPSPrefix_of_singleton
    {current tail : QuittingNashBellmanPoint ι}
    (edge : IsQuittingNashBellmanEdge reward current tail)
    (owner : ι) {mass : ℝ} (hmassPos : 0 < mass) (hmassLt : mass < 1)
    (hroot : quittingRootOfSimplex current.2 =
      quittingSoloStationaryRoot owner
        (quittingHazardCoin mass hmassPos.le hmassLt.le))
    (hviable : QuittingEssentialAPSViable reward current.1) :
    current.1 ∈ quittingProperEssentialAPSPrefix reward owner {tail.1} := by
  have harc := edge.eq_singletonArc_of_root owner
    hmassPos.le hmassLt.le hroot
  have hactive := edge.active_eq_solo_of_singleton owner
    hmassPos hmassLt hroot
  exact ⟨hviable, mass, ⟨hmassPos, hmassLt⟩,
    tail.1, Set.mem_singleton tail.1, harc, hactive⟩

/-- A finite cyclic word of viable physical singleton-root Nash--Bellman
edges, with a genuine owner change at every seam, is an executable
essential-APS cycle certificate.  Quantitative mesh and collision bounds are
supplied canonically from the finite word and the reward bound. -/
def quittingEssentialAPSCycleCertificateOfNashBellmanSingletonCycle
    {L : ℕ}
    (point : Fin L → QuittingNashBellmanPoint ι)
    (owner : Fin L → ι) (mass : Fin L → ℝ) (initial : Fin L)
    (hmassPos : ∀ block, 0 < mass block)
    (hmassLt : ∀ block, mass block < 1)
    (hroot : ∀ block, quittingRootOfSimplex (point block).2 =
      quittingSoloStationaryRoot (owner block)
        (quittingHazardCoin (mass block)
          (hmassPos block).le (hmassLt block).le))
    (hedge : ∀ block, IsQuittingNashBellmanEdge reward
      (point block) (point (finRotate L block)))
    (hviable : ∀ block,
      QuittingEssentialAPSViable reward (point block).1)
    (hownerChanges : ∀ block,
      owner block ≠ owner (finRotate L block))
    (hgeneric : IsQuittingSoloGeneric reward) :
    QuittingEssentialAPSCycleCertificate reward L where
  owner := owner
  hazard := mass
  coarse := fun block => (point block).1
  initial := initial
  intensityBound := ∑ block, quittingMeshIntensity (mass block)
  collisionBound := 2 * quittingRewardBound reward
  hazard_pos := hmassPos
  hazard_lt_one := hmassLt
  intensity_le := by
    intro block
    exact Finset.single_le_sum
      (fun other _ => quittingMeshIntensity_nonneg
        (hmassPos other).le (hmassLt other).le)
      (Finset.mem_univ block)
  collisionBound_nonneg := mul_nonneg (by norm_num)
    (quittingRewardBound_nonneg reward)
  arc := by
    intro block
    exact (hedge block).eq_singletonArc_of_root (owner block)
      (hmassPos block).le (hmassLt block).le (hroot block)
  active := by
    intro block
    exact (hedge block).active_eq_solo_of_singleton (owner block)
      (hmassPos block) (hmassLt block) (hroot block)
  viable := hviable
  collision_le := by
    intro block other _hne
    exact quittingSingletonCollisionSurplus_le_two_mul_bound
      reward (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) (owner block) other
  owner_changes := hownerChanges
  singleton_generic := hgeneric

omit [Fintype ι] in
/-- Changing singleton owners and proper masses force every player's
opponent-survival product to contract around the finite word. -/
theorem quittingSingletonCycle_opponentContracts_of_ownerChanges
    {L : ℕ} (owner : Fin L → ι) (mass : Fin L → ℝ) (initial : Fin L)
    (hmassPos : ∀ block, 0 < mass block)
    (hmassLt : ∀ block, mass block < 1)
    (hownerChanges : ∀ block,
      owner block ≠ owner (finRotate L block))
    (who : ι) :
    (∏ block : Fin L,
      if who = owner block then 1 else 1 - mass block) < 1 := by
  let factor : Fin L → ℝ := fun block ↦
    if who = owner block then 1 else 1 - mass block
  have hpositive : ∀ block ∈ Finset.univ, 0 < factor block := by
    intro block _
    simp only [factor]
    split
    · norm_num
    · exact sub_pos.mpr (hmassLt block)
  have hle : ∀ block ∈ Finset.univ, factor block ≤ (1 : ℝ) := by
    intro block _
    simp only [factor]
    split
    · exact le_rfl
    · exact sub_le_self 1 (hmassPos block).le
  have hstrict : ∃ block ∈ Finset.univ, factor block < (1 : ℝ) := by
    by_cases hwho : who = owner initial
    · refine ⟨finRotate L initial, Finset.mem_univ _, ?_⟩
      have hnext : who ≠ owner (finRotate L initial) := by
        intro h
        exact hownerChanges initial (hwho.symm.trans h)
      simp only [factor, if_neg hnext]
      linarith [hmassPos (finRotate L initial)]
    · refine ⟨initial, Finset.mem_univ _, ?_⟩
      simp only [factor, if_neg hwho]
      linarith [hmassPos initial]
  have hproduct := Finset.prod_lt_prod hpositive hle hstrict
  simpa only [Finset.prod_const_one, Finset.card_univ, one_pow,
    factor] using hproduct

/-- **Physical singleton-return compiler.**  A finite state-matched cyclic
word of proper singleton-root exact Nash--Bellman edges with viable values
delivers its selected Bellman value as a uniform-equilibrium payoff.

No genericity of the reward table is needed for this constructive conclusion.
Genericity is used by the certificate above only to recover the paper's
strict Flesch-successor graph. -/
theorem isUniformEquilibriumPayoff_of_nashBellmanSingletonCycle
    {L : ℕ}
    (point : Fin L → QuittingNashBellmanPoint ι)
    (owner : Fin L → ι) (mass : Fin L → ℝ) (initial : Fin L)
    (hmassPos : ∀ block, 0 < mass block)
    (hmassLt : ∀ block, mass block < 1)
    (hroot : ∀ block, quittingRootOfSimplex (point block).2 =
      quittingSoloStationaryRoot (owner block)
        (quittingHazardCoin (mass block)
          (hmassPos block).le (hmassLt block).le))
    (hedge : ∀ block, IsQuittingNashBellmanEdge reward
      (point block) (point (finRotate L block)))
    (hviable : ∀ block,
      QuittingEssentialAPSViable reward (point block).1)
    (hownerChanges : ∀ block,
      owner block ≠ owner (finRotate L block)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (point initial).1 := by
  exact singletonArcCycle_isUniformEquilibriumPayoff
    reward owner mass (fun block ↦ (point block).1) initial
      (aStar := ∑ block, quittingMeshIntensity (mass block))
      (D := 2 * quittingRewardBound reward)
      (fun block ↦ (hmassPos block).le) hmassLt
      (fun block ↦ Finset.single_le_sum
        (fun other _ ↦ quittingMeshIntensity_nonneg
          (hmassPos other).le (hmassLt other).le)
        (Finset.mem_univ block))
      (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
      (fun block ↦ (hedge block).eq_singletonArc_of_root (owner block)
        (hmassPos block).le (hmassLt block).le (hroot block))
      (fun block ↦ (hedge block).active_eq_solo_of_singleton
        (owner block) (hmassPos block) (hmassLt block) (hroot block))
      (fun block who ↦ hviable block who)
      (fun block other _hne ↦
        quittingSingletonCollisionSurplus_le_two_mul_bound
          reward (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward)
            (owner block) other)
      (quittingSingletonCycle_opponentContracts_of_ownerChanges
        owner mass initial hmassPos hmassLt hownerChanges)

end GameTheory
