/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailRepairValue
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryNeverCoupling

/-!
# Elementary density of the fixed-prefix behavioral-tail gain

The three-case elementary cap theorem controls the two boundary coordinates
of one behavioral tail.  This file supplies the small quantitative bridge
which turns that coordinate control into control of the actual co-realized
gain at a fixed prefix.  The prescribed and best-response coordinates remain
those of the same tail throughout; no independent boundary pairing is
introduced.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingBoundaryHolonomy

/-! ## Pairwise boundary modulus -/

/-- Exact coefficient-weighted distance between two boundary pairs for one
fixed holonomy.  The early and continue-through offsets cancel; only the two
survival slopes weight the boundary-coordinate changes. -/
def boundaryPairDistance
    (holonomy : QuittingBoundaryHolonomy ι)
    (v w v' w' : ι → ℝ) (who : ι) : ℝ :=
  (holonomy.prescribed who).survival * |v who - v' who| +
    (holonomy.bestResponse who).survival * |w who - w' who|

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem coRealizedGain_pair_lipschitz
    (holonomy : QuittingBoundaryHolonomy ι)
    (v w v' w' : ι → ℝ) (who : ι) :
    |holonomy.coRealizedGain v w who -
        holonomy.coRealizedGain v' w' who| ≤
      holonomy.boundaryPairDistance v w v' w' who := by
  have hP : 0 ≤ (holonomy.prescribed who).survival :=
    (holonomy.prescribed who).survival_nonneg
  have hχ : 0 ≤ (holonomy.bestResponse who).survival :=
    (holonomy.bestResponse who).survival_nonneg
  have htail :
      |(holonomy.bestResponse who).tail +
          (holonomy.bestResponse who).survival * w who -
        ((holonomy.bestResponse who).tail +
          (holonomy.bestResponse who).survival * w' who)| =
        (holonomy.bestResponse who).survival * |w who - w' who| := by
    rw [show (holonomy.bestResponse who).tail +
          (holonomy.bestResponse who).survival * w who -
        ((holonomy.bestResponse who).tail +
          (holonomy.bestResponse who).survival * w' who) =
        (holonomy.bestResponse who).survival * (w who - w' who) by ring,
      abs_mul, abs_of_nonneg hχ]
  have hbest :
      |holonomy.boundaryEnvelopeAt w who -
          holonomy.boundaryEnvelopeAt w' who| ≤
        (holonomy.bestResponse who).survival * |w who - w' who| := by
    rw [boundaryEnvelopeAt, boundaryEnvelopeAt,
      QuittingMaxAffineSummary.eval, QuittingMaxAffineSummary.eval]
    calc
      _ ≤ max 0 |(holonomy.bestResponse who).tail +
          (holonomy.bestResponse who).survival * w who -
          ((holonomy.bestResponse who).tail +
            (holonomy.bestResponse who).survival * w' who)| := by
        simpa using (abs_max_sub_max_le
          (holonomy.bestResponse who).early
          ((holonomy.bestResponse who).tail +
            (holonomy.bestResponse who).survival * w who)
          (holonomy.bestResponse who).early
          ((holonomy.bestResponse who).tail +
            (holonomy.bestResponse who).survival * w' who))
      _ ≤ _ := by rw [max_eq_right (abs_nonneg _)]; exact le_of_eq htail
  have hprescribed :
      |holonomy.prescribedAt v who - holonomy.prescribedAt v' who| ≤
        (holonomy.prescribed who).survival * |v who - v' who| := by
    unfold prescribedAt
    rw [QuittingAffineSummary.eval, QuittingAffineSummary.eval]
    calc
      _ = |(holonomy.prescribed who).survival *
          (v who - v' who)| := by congr 1; ring
      _ = (holonomy.prescribed who).survival * |v who - v' who| := by
        rw [abs_mul, abs_of_nonneg hP]
      _ ≤ _ := le_rfl
  unfold coRealizedGain
  calc
    _ ≤ |holonomy.boundaryEnvelopeAt w who -
          holonomy.boundaryEnvelopeAt w' who| +
        |holonomy.prescribedAt v who -
          holonomy.prescribedAt v' who| := by
      rw [show (holonomy.boundaryEnvelopeAt w who -
          holonomy.prescribedAt v who) -
          (holonomy.boundaryEnvelopeAt w' who -
            holonomy.prescribedAt v' who) =
          (holonomy.boundaryEnvelopeAt w who -
            holonomy.boundaryEnvelopeAt w' who) -
          (holonomy.prescribedAt v who -
            holonomy.prescribedAt v' who) by ring]
      calc
        _ ≤ |(holonomy.boundaryEnvelopeAt w who -
              holonomy.boundaryEnvelopeAt w' who) - 0| +
            |0 - (holonomy.prescribedAt v who -
              holonomy.prescribedAt v' who)| :=
          abs_sub_le _ _ _
        _ = _ := by rw [sub_zero, zero_sub, abs_neg]
    _ ≤ _ := by
      simpa [boundaryPairDistance, add_comm] using
        add_le_add hbest hprescribed

omit [DecidableEq ι] in
/-- Maximum-positive gain is nonexpansive under the pairwise modulus. -/
theorem maxCoRealizedGain_pair_lipschitz
    (holonomy : QuittingBoundaryHolonomy ι)
    (v w v' w' : ι → ℝ) :
    |holonomy.maxCoRealizedGain v w -
        holonomy.maxCoRealizedGain v' w'| ≤
      finitePlayerMax (holonomy.boundaryPairDistance v w v' w') := by
  have hpoint (who : ι) :
      |max 0 (holonomy.coRealizedGain v w who) -
          max 0 (holonomy.coRealizedGain v' w' who)| ≤
        holonomy.boundaryPairDistance v w v' w' who := by
    calc
      _ ≤ |holonomy.coRealizedGain v w who -
          holonomy.coRealizedGain v' w' who| := by
        simpa using (abs_max_sub_max_le 0
          (holonomy.coRealizedGain v w who) 0
          (holonomy.coRealizedGain v' w' who))
      _ ≤ _ := coRealizedGain_pair_lipschitz holonomy v w v' w' who
  let f := fun who => max 0 (holonomy.coRealizedGain v w who)
  let g := fun who => max 0 (holonomy.coRealizedGain v' w' who)
  let D := finitePlayerMax (holonomy.boundaryPairDistance v w v' w')
  have hfg (who : ι) : f who ≤ finitePlayerMax g + D := by
    have h := hpoint who
    have hD := le_finitePlayerMax (holonomy.boundaryPairDistance v w v' w') who
    have h' : |f who - g who| ≤ D := by
      dsimp [f, g]
      exact h.trans hD
    have hdiff : f who - g who ≤ D :=
      (le_abs_self (f who - g who)).trans h'
    have hgmax := le_finitePlayerMax g who
    exact (by linarith : f who ≤ finitePlayerMax g + D)
  have hgf (who : ι) : g who ≤ finitePlayerMax f + D := by
    have h := hpoint who
    have hD := le_finitePlayerMax (holonomy.boundaryPairDistance v w v' w') who
    have h' : |f who - g who| ≤ D := by
      dsimp [f, g]
      exact h.trans hD
    have hdiff : g who - f who ≤ D := by
      have hneg : g who - f who ≤ |f who - g who| := by
        simpa [abs_sub_comm] using le_abs_self (g who - f who)
      exact hneg.trans h'
    have hfmax := le_finitePlayerMax f who
    exact (by linarith : g who ≤ finitePlayerMax f + D)
  have hup : finitePlayerMax f ≤ finitePlayerMax g + D := by
    apply finitePlayerMax_le
    exact hfg
  have hlow : finitePlayerMax g ≤ finitePlayerMax f + D := by
    apply finitePlayerMax_le
    exact hgf
  dsimp [maxCoRealizedGain, f, g]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## Specialization to actual finite quitting prefixes -/

omit [Nonempty ι] in
/-- Actual finite quitting holonomies have both survival coefficients at most
one, so the exact pair modulus is bounded by the unweighted coordinate error.
-/
theorem quittingFiniteBoundaryHolonomy_boundaryPairDistance_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start extra : ℕ)
    (v w v' w' : ι → ℝ) (who : ι) :
    boundaryPairDistance
        (quittingFiniteBoundaryHolonomy reward roots start extra)
        v w v' w' who ≤ |v who - v' who| + |w who - w' who| := by
  let holonomy := quittingFiniteBoundaryHolonomy reward roots start extra
  have hP := (quittingFiniteBoundaryHolonomy_coordinates_bounded
    reward roots start extra who).2.1
  have hχ := (quittingFiniteBoundaryHolonomy_coordinates_bounded
    reward roots start extra who).2.2.2.2
  dsimp [boundaryPairDistance]
  have hv := abs_nonneg (v who - v' who)
  have hw := abs_nonneg (w who - w' who)
  nlinarith [mul_le_mul_of_nonneg_right hP hv,
    mul_le_mul_of_nonneg_right hχ hw]

/-! ## Elementary cap density -/

/-- One elementary terminal cap approximates the co-realized gain of any
behavioral tail at one actual finite prefix.  The selector is the complete
Never/sure-joint/sure-solo trichotomy; the two tail coordinates are supplied
by that same selected cap. -/
theorem exists_elementaryTailCap_behavioralTailGain_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (prefixRoots : ℕ → ι → PMF Bool) (start extra : ℕ)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      |(quittingFiniteBoundaryHolonomy reward prefixRoots start extra).maxCoRealizedGain
          (behavioralTailPrescribedBoundary reward roots)
          (behavioralTailEnvelopeBoundary reward roots) -
        (quittingFiniteBoundaryHolonomy reward prefixRoots start extra).maxCoRealizedGain
          (behavioralTailPrescribedBoundary reward
            (quittingElementaryTailRoots roots cutoff cap))
          (behavioralTailEnvelopeBoundary reward
            (quittingElementaryTailRoots roots cutoff cap))| < ε := by
  let holonomy := quittingFiniteBoundaryHolonomy reward prefixRoots start extra
  obtain ⟨cap, cutoff, hp, hb⟩ :=
    exists_elementaryTailCap_terminalPair_close reward roots
      (M := M) (ε := ε / 4) hM (by linarith) hreward
  refine ⟨cap, cutoff, ?_⟩
  have hpair :
      finitePlayerMax (holonomy.boundaryPairDistance
        (behavioralTailPrescribedBoundary reward roots)
        (behavioralTailEnvelopeBoundary reward roots)
        (behavioralTailPrescribedBoundary reward
          (quittingElementaryTailRoots roots cutoff cap))
        (behavioralTailEnvelopeBoundary reward
          (quittingElementaryTailRoots roots cutoff cap))) < ε / 2 := by
    dsimp [finitePlayerMax]
    rw [Finset.sup'_lt_iff]
    intro who hwho
    calc
      _ ≤ |behavioralTailPrescribedBoundary reward roots who -
            behavioralTailPrescribedBoundary reward
              (quittingElementaryTailRoots roots cutoff cap) who| +
          |behavioralTailEnvelopeBoundary reward roots who -
            behavioralTailEnvelopeBoundary reward
              (quittingElementaryTailRoots roots cutoff cap) who| :=
        quittingFiniteBoundaryHolonomy_boundaryPairDistance_le
          reward prefixRoots start extra _ _ _ _ who
      _ < ε / 2 := by
        have hp' := hp who
        have hb' := hb who
        change |behavioralTailPrescribedBoundary reward roots who -
          behavioralTailPrescribedBoundary reward
            (quittingElementaryTailRoots roots cutoff cap) who| < ε / 4 at hp'
        change |behavioralTailEnvelopeBoundary reward roots who -
          behavioralTailEnvelopeBoundary reward
            (quittingElementaryTailRoots roots cutoff cap) who| < ε / 4 at hb'
        linarith
  exact (maxCoRealizedGain_pair_lipschitz holonomy _ _ _ _).trans_lt
    (lt_trans hpair (by linarith))

/-! ## Infimum over elementary capped tails -/

/-- Index for an elementary capped tail: a source tail, its elementary cap,
and the cutoff at which the cap is attached. -/
abbrev ElementaryTailIndex (ι : Type) :=
  (ℕ → ι → PMF Bool) × (QuittingElementaryTailCap ι × ℕ)

/-- The fixed-prefix gain of an elementary capped tail.  This is merely the
behavioral-tail gain of the capped root sequence, so its two boundary values
remain co-realized by construction. -/
def elementaryTailGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (holonomy : QuittingBoundaryHolonomy ι)
    (index : ElementaryTailIndex ι) : ℝ :=
  behavioralTailGain reward holonomy
    (quittingElementaryTailRoots index.1 index.2.2 index.2.1)

/-- The infimum of the elementary capped-tail family. -/
def elementaryTailRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (holonomy : QuittingBoundaryHolonomy ι) : ℝ :=
  sInf (Set.range (elementaryTailGain reward holonomy))

theorem bddBelow_range_elementaryTailGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (holonomy : QuittingBoundaryHolonomy ι) :
    BddBelow (Set.range (elementaryTailGain reward holonomy)) := by
  refine ⟨0, ?_⟩
  rintro value ⟨index, rfl⟩
  exact behavioralTailGain_nonneg reward holonomy _

theorem elementaryTailGain_range_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (holonomy : QuittingBoundaryHolonomy ι) :
    (Set.range (elementaryTailGain reward holonomy)).Nonempty := by
  refine ⟨elementaryTailGain reward holonomy
      ((fun _ _ => PMF.pure false), (.never, 0)), ?_⟩
  exact ⟨((fun _ _ => PMF.pure false), (.never, 0)), rfl⟩

/-- Elementary capped tails are a subfamily of all behavioral tails. -/
theorem elementaryTailGain_range_subset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (holonomy : QuittingBoundaryHolonomy ι) :
    Set.range (elementaryTailGain reward holonomy) ⊆
      Set.range (behavioralTailGain reward holonomy) := by
  rintro value ⟨index, rfl⟩
  exact ⟨quittingElementaryTailRoots index.1 index.2.2 index.2.1, rfl⟩

/-- For every actual finite prefix, elementary capped tails have the same
infimum as all behavioral tails.  The forward inequality is range inclusion;
the reverse inequality uses pointwise density and the elementary infimum as a
strict separator, so neither infimum needs to be attained. -/
theorem elementaryTailRepairValue_eq_behavioralTailRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefixRoots : ℕ → ι → PMF Bool) (start extra : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    elementaryTailRepairValue reward
        (quittingFiniteBoundaryHolonomy reward prefixRoots start extra) =
      behavioralTailRepairValue reward
        (quittingFiniteBoundaryHolonomy reward prefixRoots start extra) := by
  let holonomy := quittingFiniteBoundaryHolonomy reward prefixRoots start extra
  let elementary := Set.range (elementaryTailGain reward holonomy)
  let behavioral := Set.range (behavioralTailGain reward holonomy)
  have hbelowE : BddBelow elementary := by
    simpa [elementary] using bddBelow_range_elementaryTailGain reward holonomy
  have hneE : elementary.Nonempty := by
    simpa [elementary] using elementaryTailGain_range_nonempty reward holonomy
  have hbelowB : BddBelow behavioral := by
    simpa [behavioral] using bddBelow_range_behavioralTailGain reward holonomy
  have hneB : behavioral.Nonempty := Set.range_nonempty _
  have hsub : elementary ⊆ behavioral := by
    simpa [elementary, behavioral] using
      elementaryTailGain_range_subset reward holonomy
  have hforward : sInf behavioral ≤ sInf elementary :=
    csInf_le_csInf hbelowB hneE hsub
  have hreverse : sInf elementary ≤ sInf behavioral := by
    apply le_csInf hneB
    rintro value ⟨roots, rfl⟩
    by_contra hnot
    have hlt : behavioralTailGain reward holonomy roots < sInf elementary :=
      lt_of_not_ge hnot
    let δ := (sInf elementary - behavioralTailGain reward holonomy roots) / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    obtain ⟨cap, cutoff, hclose⟩ :=
      exists_elementaryTailCap_behavioralTailGain_close
        reward roots prefixRoots start extra hM hδ hreward
    let index : ElementaryTailIndex ι := (roots, (cap, cutoff))
    have hle := csInf_le hbelowE ⟨index, rfl⟩
    have hupper : elementaryTailGain reward holonomy index <
        behavioralTailGain reward holonomy roots + δ := by
      change behavioralTailGain reward holonomy
          (quittingElementaryTailRoots roots cutoff cap) <
        behavioralTailGain reward holonomy roots + δ
      have hclose' := hclose
      change |behavioralTailGain reward holonomy roots -
        behavioralTailGain reward
          holonomy
          (quittingElementaryTailRoots roots cutoff cap)| < δ at hclose'
      have hlower' := (abs_lt.mp hclose').1
      linarith
    have hcap : elementaryTailGain reward holonomy index < sInf elementary := by
      change behavioralTailGain reward holonomy
          (quittingElementaryTailRoots roots cutoff cap) < sInf elementary
      dsimp [δ] at hupper
      linarith
    exact (not_lt_of_ge hle) hcap
  dsimp [elementaryTailRepairValue, behavioralTailRepairValue]
  exact le_antisymm hreverse hforward

end QuittingBoundaryHolonomy

end GameTheory
