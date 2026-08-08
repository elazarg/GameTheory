/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.Basic

/-!
# Fixed-prefix all-tail repair modulus

This module formalizes the fixed-prefix part of the bounded-compression
decision.  A tail is represented only by its co-realized prescribed and
unilateral boundary values `(v,w)`.  The prefix holonomy then gives the
literal payoff and best-response gain.  The modulus below is uniform over
all such pairs in a coordinate box; it makes no claim about tail density,
tail construction, or global exploitability.

The fixed-family infimum result is deliberately phrased for an arbitrary
source-independent family of boundary pairs.
-/

noncomputable section

namespace GameTheory

variable {ι : Type}

namespace QuittingBoundaryHolonomy

/-! ## Co-realized boundary gains -/

/-- Prescribed payoff after attaching coordinate `v` at the fixed prefix. -/
def prescribedAt (holonomy : QuittingBoundaryHolonomy ι)
    (v : ι → ℝ) (who : ι) : ℝ :=
  (holonomy.prescribed who).eval (v who)

/-- Boundary best-response envelope evaluation after attaching coordinate `w`.
It is the literal best response when `w` is the co-realized value of the same
tail as `v`; no such provenance is asserted for an arbitrary pair here. -/
def boundaryEnvelopeAt (holonomy : QuittingBoundaryHolonomy ι)
    (w : ι → ℝ) (who : ι) : ℝ :=
  (holonomy.bestResponse who).eval (w who)

/-- The fixed-prefix gain at a co-realized boundary pair. -/
def coRealizedGain (holonomy : QuittingBoundaryHolonomy ι)
    (v w : ι → ℝ) (who : ι) : ℝ :=
  holonomy.boundaryEnvelopeAt w who - holonomy.prescribedAt v who

/-- Coordinate-weighted distance between two fixed-prefix holonomies. -/
def coordinateDistance (M : ℝ)
    (holonomy holonomy' : QuittingBoundaryHolonomy ι) (who : ι) : ℝ :=
  |(holonomy.bestResponse who).early -
      (holonomy'.bestResponse who).early| +
    |(holonomy.bestResponse who).tail -
      (holonomy'.bestResponse who).tail| +
    M * |(holonomy.bestResponse who).survival -
      (holonomy'.bestResponse who).survival| +
    |(holonomy.prescribed who).intercept -
      (holonomy'.prescribed who).intercept| +
    M * |(holonomy.prescribed who).survival -
      (holonomy'.prescribed who).survival|

theorem coRealizedGain_eq_coefficients
    (holonomy : QuittingBoundaryHolonomy ι) (v w : ι → ℝ) (who : ι) :
    holonomy.coRealizedGain v w who =
      max (holonomy.bestResponse who).early
          ((holonomy.bestResponse who).tail +
            (holonomy.bestResponse who).survival * w who) -
        ((holonomy.prescribed who).intercept +
          (holonomy.prescribed who).survival * v who) := by
  rfl

/-- The scalar maximum is nonexpansive in the two displayed arguments. -/
theorem abs_max_sub_max_le
    (a b a' b' : ℝ) :
    |max a b - max a' b'| ≤ max |a - a'| |b - b'| := by
  let R := max |a - a'| |b - b'|
  have hR1 : |a - a'| ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hR2 : |b - b'| ≤ R := by
    dsimp [R]
    exact le_max_right _ _
  have haa : a ≤ a' + R := by
    linarith [le_abs_self (a - a')]
  have hbb : b ≤ b' + R := by
    linarith [le_abs_self (b - b')]
  have haa' : a' ≤ a + R := by
    have h : a' - a ≤ |a - a'| := by
      simpa [abs_sub_comm] using le_abs_self (a' - a)
    linarith
  have hbb' : b' ≤ b + R := by
    have h : b' - b ≤ |b - b'| := by
      simpa [abs_sub_comm] using le_abs_self (b' - b)
    linarith
  have hup : max a b ≤ max a' b' + R := by
    apply max_le
    · exact haa.trans (by linarith [le_max_left a' b'])
    · exact hbb.trans (by linarith [le_max_right a' b'])
  have hlow : max a' b' ≤ max a b + R := by
    apply max_le
    · exact haa'.trans (by linarith [le_max_left a b])
    · exact hbb'.trans (by linarith [le_max_right a b])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem coRealizedGain_lipschitz
    (M : ℝ)
    (holonomy holonomy' : QuittingBoundaryHolonomy ι)
    (v w : ι → ℝ)
    (hv : ∀ who, |v who| ≤ M)
    (hw : ∀ who, |w who| ≤ M) (who : ι) :
    |holonomy.coRealizedGain v w who -
        holonomy'.coRealizedGain v w who| ≤
      holonomy.coordinateDistance M holonomy' who := by
  have htail :
      |(holonomy.bestResponse who).tail +
          (holonomy.bestResponse who).survival * w who -
        ((holonomy'.bestResponse who).tail +
          (holonomy'.bestResponse who).survival * w who)| ≤
        |(holonomy.bestResponse who).tail -
            (holonomy'.bestResponse who).tail| +
          M * |(holonomy.bestResponse who).survival -
            (holonomy'.bestResponse who).survival| := by
    calc
      _ = |((holonomy.bestResponse who).tail -
            (holonomy'.bestResponse who).tail) +
          ((holonomy.bestResponse who).survival -
            (holonomy'.bestResponse who).survival) * w who| := by
            congr 1
            ring_nf
      _ ≤ |(holonomy.bestResponse who).tail -
            (holonomy'.bestResponse who).tail| +
          |((holonomy.bestResponse who).survival -
            (holonomy'.bestResponse who).survival) * w who| :=
            abs_add_le _ _
      _ = |(holonomy.bestResponse who).tail -
            (holonomy'.bestResponse who).tail| +
          |(holonomy.bestResponse who).survival -
            (holonomy'.bestResponse who).survival| * |w who| := by
            rw [abs_mul]
      _ ≤ |(holonomy.bestResponse who).tail -
            (holonomy'.bestResponse who).tail| +
          |(holonomy.bestResponse who).survival -
            (holonomy'.bestResponse who).survival| * M := by
            gcongr
            exact hw who
      _ = |(holonomy.bestResponse who).tail -
            (holonomy'.bestResponse who).tail| +
          M * |(holonomy.bestResponse who).survival -
            (holonomy'.bestResponse who).survival| := by ring_nf
  have hprescribed :
      |(holonomy.prescribed who).intercept +
          (holonomy.prescribed who).survival * v who -
        ((holonomy'.prescribed who).intercept +
          (holonomy'.prescribed who).survival * v who)| ≤
        |(holonomy.prescribed who).intercept -
            (holonomy'.prescribed who).intercept| +
          M * |(holonomy.prescribed who).survival -
            (holonomy'.prescribed who).survival| := by
    calc
      _ = |((holonomy.prescribed who).intercept -
            (holonomy'.prescribed who).intercept) +
          ((holonomy.prescribed who).survival -
            (holonomy'.prescribed who).survival) * v who| := by
            congr 1
            ring_nf
      _ ≤ |(holonomy.prescribed who).intercept -
            (holonomy'.prescribed who).intercept| +
          |((holonomy.prescribed who).survival -
            (holonomy'.prescribed who).survival) * v who| :=
            abs_add_le _ _
      _ = |(holonomy.prescribed who).intercept -
            (holonomy'.prescribed who).intercept| +
          |(holonomy.prescribed who).survival -
            (holonomy'.prescribed who).survival| * |v who| := by
            rw [abs_mul]
      _ ≤ |(holonomy.prescribed who).intercept -
            (holonomy'.prescribed who).intercept| +
          |(holonomy.prescribed who).survival -
            (holonomy'.prescribed who).survival| * M := by
            gcongr
            exact hv who
      _ = |(holonomy.prescribed who).intercept -
            (holonomy'.prescribed who).intercept| +
          M * |(holonomy.prescribed who).survival -
            (holonomy'.prescribed who).survival| := by ring_nf
  have hbest :
      |holonomy.boundaryEnvelopeAt w who -
          holonomy'.boundaryEnvelopeAt w who| ≤
        |(holonomy.bestResponse who).early -
            (holonomy'.bestResponse who).early| +
          |(holonomy.bestResponse who).tail -
            (holonomy'.bestResponse who).tail| +
          M * |(holonomy.bestResponse who).survival -
            (holonomy'.bestResponse who).survival| := by
    rw [boundaryEnvelopeAt, boundaryEnvelopeAt,
      QuittingMaxAffineSummary.eval, QuittingMaxAffineSummary.eval]
    calc
      _ ≤ max |(holonomy.bestResponse who).early -
            (holonomy'.bestResponse who).early|
            |(holonomy.bestResponse who).tail +
              (holonomy.bestResponse who).survival * w who -
              ((holonomy'.bestResponse who).tail +
                (holonomy'.bestResponse who).survival * w who)| :=
          abs_max_sub_max_le _ _ _ _
      _ ≤ |(holonomy.bestResponse who).early -
            (holonomy'.bestResponse who).early| +
          |(holonomy.bestResponse who).tail +
              (holonomy.bestResponse who).survival * w who -
              ((holonomy'.bestResponse who).tail +
                (holonomy'.bestResponse who).survival * w who)| := by
            apply max_le <;>
              linarith [abs_nonneg ((holonomy.bestResponse who).early -
                (holonomy'.bestResponse who).early),
                abs_nonneg ((holonomy.bestResponse who).tail +
                  (holonomy.bestResponse who).survival * w who -
                  ((holonomy'.bestResponse who).tail +
                    (holonomy'.bestResponse who).survival * w who))]
      _ ≤ _ := by linarith
  have hgain :
      |holonomy.coRealizedGain v w who -
          holonomy'.coRealizedGain v w who| ≤
        |holonomy.boundaryEnvelopeAt w who -
            holonomy'.boundaryEnvelopeAt w who| +
          |holonomy.prescribedAt v who -
            holonomy'.prescribedAt v who| := by
    unfold coRealizedGain
    calc
      _ ≤ |(holonomy.boundaryEnvelopeAt w who - holonomy.prescribedAt v who) -
          (holonomy'.boundaryEnvelopeAt w who - holonomy.prescribedAt v who)| +
          |(holonomy'.boundaryEnvelopeAt w who - holonomy.prescribedAt v who) -
          (holonomy'.boundaryEnvelopeAt w who - holonomy'.prescribedAt v who)| := by
        exact abs_sub_le _ _ _
      _ ≤ |holonomy.boundaryEnvelopeAt w who -
            holonomy'.boundaryEnvelopeAt w who| +
          |holonomy.prescribedAt v who -
            holonomy'.prescribedAt v who| := by
        calc
          |(holonomy.boundaryEnvelopeAt w who -
                holonomy.prescribedAt v who) -
              (holonomy'.boundaryEnvelopeAt w who -
                holonomy.prescribedAt v who)| +
              |(holonomy'.boundaryEnvelopeAt w who -
                holonomy.prescribedAt v who) -
              (holonomy'.boundaryEnvelopeAt w who -
                holonomy'.prescribedAt v who)| =
              |holonomy.boundaryEnvelopeAt w who -
                holonomy'.boundaryEnvelopeAt w who| +
              |holonomy.prescribedAt v who -
                holonomy'.prescribedAt v who| := by
            congr 1
            · ring_nf
            · rw [show (holonomy'.boundaryEnvelopeAt w who -
                  holonomy.prescribedAt v who) -
                (holonomy'.boundaryEnvelopeAt w who -
                  holonomy'.prescribedAt v who) =
                -(holonomy.prescribedAt v who -
              holonomy'.prescribedAt v who) by ring_nf, abs_neg]
          _ ≤ _ := le_rfl
  have hpay :
      |holonomy.prescribedAt v who -
          holonomy'.prescribedAt v who| ≤
        |(holonomy.prescribed who).intercept -
            (holonomy'.prescribed who).intercept| +
          M * |(holonomy.prescribed who).survival -
            (holonomy'.prescribed who).survival| := by
    unfold prescribedAt
    rw [QuittingAffineSummary.eval, QuittingAffineSummary.eval]
    exact hprescribed
  unfold coordinateDistance
  linarith

/-! ## Finite-player aggregate gain -/

/-- Maximum of a real-valued quantity over the nonempty finite player set. -/
def finitePlayerMax [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

theorem finitePlayerMax_le [Fintype ι] [Nonempty ι]
    {f : ι → ℝ} {bound : ℝ}
    (hf : ∀ who, f who ≤ bound) : finitePlayerMax f ≤ bound := by
  dsimp [finitePlayerMax]
  exact Finset.sup'_le Finset.univ_nonempty f (fun who _ => hf who)

theorem le_finitePlayerMax [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (who : ι) :
    f who ≤ finitePlayerMax f := by
  dsimp [finitePlayerMax]
  exact Finset.le_sup' f (Finset.mem_univ who)

/-- Maximum positive gain over the fixed prefix at a co-realized pair. -/
def maxCoRealizedGain [Fintype ι] [Nonempty ι]
    (holonomy : QuittingBoundaryHolonomy ι)
    (v w : ι → ℝ) : ℝ :=
  finitePlayerMax (fun who => max 0 (holonomy.coRealizedGain v w who))

/-- Maximum coordinate distance between two fixed-prefix holonomies. -/
def maxCoordinateDistance [Fintype ι] [Nonempty ι] (M : ℝ)
    (holonomy holonomy' : QuittingBoundaryHolonomy ι) : ℝ :=
  finitePlayerMax (holonomy.coordinateDistance M holonomy')

theorem maxCoRealizedGain_lipschitz
    [Fintype ι] [Nonempty ι]
    (M : ℝ) (holonomy holonomy' : QuittingBoundaryHolonomy ι)
    (v w : ι → ℝ)
    (hv : ∀ who, |v who| ≤ M)
    (hw : ∀ who, |w who| ≤ M) :
    |holonomy.maxCoRealizedGain v w -
        holonomy'.maxCoRealizedGain v w| ≤
      maxCoordinateDistance M holonomy holonomy' := by
  have hpoint (who : ι) :
      |max 0 (holonomy.coRealizedGain v w who) -
          max 0 (holonomy'.coRealizedGain v w who)| ≤
        holonomy.coordinateDistance M holonomy' who := by
    calc
      _ ≤ |holonomy.coRealizedGain v w who -
          holonomy'.coRealizedGain v w who| := by
        simpa using
          (abs_max_sub_max_le 0 (holonomy.coRealizedGain v w who)
            0 (holonomy'.coRealizedGain v w who))
      _ ≤ _ := coRealizedGain_lipschitz M holonomy holonomy' v w hv hw who
  let f := fun who => max 0 (holonomy.coRealizedGain v w who)
  let g := fun who => max 0 (holonomy'.coRealizedGain v w who)
  let D := maxCoordinateDistance M holonomy holonomy'
  have hfg (who : ι) : f who ≤ finitePlayerMax g + D := by
    have h := hpoint who
    have hD := le_finitePlayerMax (holonomy.coordinateDistance M holonomy') who
    have h' : |f who - g who| ≤ D := by
      dsimp [f, g]
      exact h.trans hD
    have hdiff : f who - g who ≤ D :=
      (le_abs_self (f who - g who)).trans h'
    have hgmax := le_finitePlayerMax g who
    exact (by linarith : f who ≤ finitePlayerMax g + D)
  have hgf (who : ι) : g who ≤ finitePlayerMax f + D := by
    have h := hpoint who
    have hD := le_finitePlayerMax (holonomy.coordinateDistance M holonomy') who
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

/-! ## Fixed-family infima and buffered transfer -/

/-- A common pointwise modulus survives an infimum over one fixed family. -/
theorem sInf_range_lipschitz_of_common_modulus
    {α : Type*} [Nonempty α] (F G : α → ℝ) (D : ℝ)
    (hF : BddBelow (Set.range F)) (hG : BddBelow (Set.range G))
    (hFG : ∀ a, F a ≤ G a + D)
    (hGF : ∀ a, G a ≤ F a + D) :
    |sInf (Set.range F) - sInf (Set.range G)| ≤ D := by
  have hFG' : sInf (Set.range F) ≤ sInf (Set.range G) + D := by
    by_contra hcontra
    have hlt : sInf (Set.range G) < sInf (Set.range F) - D := by
      linarith
    obtain ⟨a, ha, ha_lt⟩ :=
      exists_lt_of_csInf_lt (Set.range_nonempty G) hlt
    rcases ha with ⟨a, rfl⟩
    have hFa : sInf (Set.range F) ≤ F a :=
      csInf_le hF ⟨a, rfl⟩
    have hFlt : F a < sInf (Set.range F) := by
      linarith [hFG a]
    exact (not_lt_of_ge hFa) hFlt
  have hGF' : sInf (Set.range G) ≤ sInf (Set.range F) + D := by
    by_contra hcontra
    have hlt : sInf (Set.range F) < sInf (Set.range G) - D := by
      linarith
    obtain ⟨a, ha, ha_lt⟩ :=
      exists_lt_of_csInf_lt (Set.range_nonempty F) hlt
    rcases ha with ⟨a, rfl⟩
    have hGa : sInf (Set.range G) ≤ G a :=
      csInf_le hG ⟨a, rfl⟩
    have hGlt : G a < sInf (Set.range G) := by
      linarith [hGF a]
    exact (not_lt_of_ge hGa) hGlt
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A fixed witness transfers from a buffered center to nearby holonomies. -/
theorem fixedFamily_repair_transfer
    {α : Type*} (F : QuittingBoundaryHolonomy ι → α → ℝ)
    (H H₀ : QuittingBoundaryHolonomy ι) (ε D : ℝ) (a₀ : α)
    (hmod : ∀ a, |F H a - F H₀ a| ≤ D)
    (hcenter : F H₀ a₀ < ε / 4) (hclose : D < ε / 4) :
    F H a₀ < ε / 2 := by
  have hdiff := hmod a₀
  linarith [le_abs_self (F H a₀ - F H₀ a₀)]

/-- A positive fixed-family infimum transfers to every member nearby. -/
theorem fixedFamily_obstruction_transfer
    {α : Type*} (F : QuittingBoundaryHolonomy ι → α → ℝ)
    (H H₀ : QuittingBoundaryHolonomy ι) (ε D : ℝ)
    (hmod : ∀ a, |F H a - F H₀ a| ≤ D)
    (hbelow : BddBelow (Set.range (F H₀)))
    (hinf : ε / 4 ≤ sInf (Set.range (F H₀)))
    (hclose : D < ε / 8) (a : α) :
    ε / 8 ≤ F H a := by
  have hcenter : ε / 4 ≤ F H₀ a :=
    hinf.trans (csInf_le hbelow ⟨a, rfl⟩)
  have hdiff := hmod a
  have hrev : F H₀ a - F H a ≤ D := by
    have habs : |F H₀ a - F H a| ≤ D := by
      simpa [abs_sub_comm] using hdiff
    exact (le_abs_self _).trans habs
  linarith

end QuittingBoundaryHolonomy

end GameTheory
