/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.Probability.AnalyticOccupationFlow
import Math.Probability.ChargedOccupationAlternative

/-!
# Analytic Charged Occupation-Flow Alternative

For finite analytic families of occupation columns and scalar charges, charged
circulation feasibility has an eventually constant truth value. In the
feasible branch, one fixed Cramer support gives a pole-cleared analytic
nonnegative circulation whose total charge is an exact power of the
parameter. In the infeasible branch, the charged Farkas potential can likewise
be selected analytically after clearing one common pole.

This is a punctured-germ theorem. It deliberately makes no claim that a
charged circulation existing only at the endpoint persists at positive
parameters.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Filter LinearAlgebra Set

variable {S I : Type*}

/-- A pole-cleared analytic nonnegative circulation with an exact positive
power-law total charge. -/
structure AnalyticPositiveChargedCirculation
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (charge : ℝ → I → ℝ) where
  poleOrder : ℕ
  mass : ℝ → I → ℝ
  analytic_mass : AnalyticAt ℝ mass 0
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (∀ i, 0 ≤ mass t i) ∧
        (∀ destination,
          ∑ i, mass t i * column t i destination = 0) ∧
        (∑ i, mass t i * charge t i) = t ^ poleOrder

/-- A pole-cleared analytic charged-occupation potential. The common power
multiplies every charge, while the potential itself is analytic at the
endpoint. -/
structure AnalyticScaledChargedOccupationPotential
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (charge : ℝ → I → ℝ) where
  poleOrder : ℕ
  potential : ℝ → S → ℝ
  analytic_potential : AnalyticAt ℝ potential 0
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ i, t ^ poleOrder * charge t i ≤
        ∑ destination,
          potential t destination * column t i destination

namespace AnalyticPositiveChargedCirculation

/-- A pole-cleared charged circulation normalizes to an ordinary positive
charged circulation at every sufficiently small positive parameter. -/
theorem eventually_hasNormalizedPositiveChargedCirculation
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticPositiveChargedCirculation column charge) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      HasNormalizedPositiveChargedCirculation (column t) (charge t) := by
  filter_upwards [C.eventual, self_mem_nhdsWithin] with t ht htpos
  exact exists_normalizedPositiveChargedCirculation_of_pos
    ht.1 ht.2.1 (by
      rw [ht.2.2]
      exact pow_pos (mem_Ioi.mp htpos) _)

end AnalyticPositiveChargedCirculation

namespace AnalyticScaledChargedOccupationPotential

/-- Dividing a pole-cleared potential by its positive clearing power gives an
ordinary charged-occupation potential on the punctured interval. -/
theorem eventually_exists_chargedOccupationPotential
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {charge : ℝ → I → ℝ}
    (C : AnalyticScaledChargedOccupationPotential column charge) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∃ potential : S → ℝ,
        IsChargedOccupationPotential (column t) (charge t) potential := by
  filter_upwards [C.eventual, self_mem_nhdsWithin] with t ht htpos
  have hpow : 0 < t ^ C.poleOrder :=
    pow_pos (mem_Ioi.mp htpos) _
  let potential : S → ℝ :=
    fun destination => C.potential t destination / t ^ C.poleOrder
  refine ⟨potential, fun i => ?_⟩
  have hsum :
      (∑ destination,
          potential destination * column t i destination) =
        (∑ destination,
          C.potential t destination * column t i destination) /
            t ^ C.poleOrder := by
    simp only [potential, div_mul_eq_mul_div]
    rw [Finset.sum_div]
  rw [hsum]
  apply (le_div_iff₀ hpow).2
  simpa only [mul_comm] using ht i

end AnalyticScaledChargedOccupationPotential

/-- Nonnegative variables encoding a signed potential, one nonnegative slack
per charged column, and a nonnegative homogenizing coordinate. -/
abbrev AnalyticChargedPotentialVariable (S I : Type*) :=
  Sum (S × Bool) (Sum I Unit)

/-- Equality system for a scaled charged-occupation potential:
`⟨h, column i⟩ - slack i - scale * charge i = 0`. -/
def analyticChargedPotentialBalance
    [DecidableEq I]
    (column : ℝ → I → S → ℝ) (charge : ℝ → I → ℝ) :
    ℝ → Matrix I (AnalyticChargedPotentialVariable S I) ℝ :=
  fun t i entry =>
    match entry with
    | Sum.inl oriented =>
        farkasOrientation oriented.2 * column t i oriented.1
    | Sum.inr (Sum.inl slack) =>
        if slack = i then -1 else 0
    | Sum.inr (Sum.inr _) => -charge t i

/-- The normalizing functional selects the homogenizing coordinate. -/
def analyticChargedPotentialScale :
    AnalyticChargedPotentialVariable S I → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr _) => 1

/-- Recover the signed potential from its doubled nonnegative coordinates. -/
def analyticChargedPotential
    (z : AnalyticChargedPotentialVariable S I → ℝ) : S → ℝ :=
  fun destination =>
    z (Sum.inl (destination, true)) -
      z (Sum.inl (destination, false))

theorem analyticChargedPotentialBalance_mulVec
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (charge : I → ℝ)
    (z : AnalyticChargedPotentialVariable S I → ℝ) (i : I) :
    Matrix.mulVec
        (analyticChargedPotentialBalance
          (fun _ => column) (fun _ => charge) 0) z i =
      (∑ destination,
          analyticChargedPotential z destination *
            column i destination) -
        z (Sum.inr (Sum.inl i)) -
        charge i * z (Sum.inr (Sum.inr PUnit.unit)) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have horiented :
      (∑ coordinate : S × Bool,
          (farkasOrientation coordinate.2 *
              column i coordinate.1) *
            z (Sum.inl coordinate)) =
        ∑ destination,
          analyticChargedPotential z destination *
            column i destination := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro destination _
    simp [farkasOrientation, analyticChargedPotential]
    ring
  simp only [analyticChargedPotentialBalance]
  rw [horiented]
  simp
  ring

theorem analyticChargedPotentialScale_dotProduct
    [Fintype S] [Fintype I]
    (z : AnalyticChargedPotentialVariable S I → ℝ) :
    (∑ entry, analyticChargedPotentialScale entry * z entry) =
      z (Sum.inr (Sum.inr PUnit.unit)) := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [analyticChargedPotentialScale]

/-- Every ordinary charged-occupation potential gives a nonnegative
normalized certificate in the affine correction system. -/
theorem normalizedFarkasCertificateSet_chargedPotential_nonempty
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (charge : I → ℝ)
    (hpotential :
      ∃ potential, IsChargedOccupationPotential column charge potential) :
    (normalizedFarkasCertificateSet
      (analyticChargedPotentialBalance
        (fun _ => column) (fun _ => charge) 0)
      (analyticChargedPotentialScale :
        AnalyticChargedPotentialVariable S I → ℝ)).Nonempty := by
  classical
  obtain ⟨potential, hpotential⟩ := hpotential
  let oriented : S × Bool → ℝ :=
    signedFarkasToOriented potential
  let slack : I → ℝ := fun i =>
    (∑ destination, potential destination * column i destination) -
      charge i
  let z : AnalyticChargedPotentialVariable S I → ℝ
    | Sum.inl coordinate => oriented coordinate
    | Sum.inr (Sum.inl i) => slack i
    | Sum.inr (Sum.inr _) => 1
  refine ⟨z, ?_, ?_⟩
  · intro entry
    cases entry with
    | inl coordinate =>
        exact signedFarkasToOriented_nonneg potential coordinate
    | inr entry =>
        cases entry with
        | inl i =>
            dsimp only [z, slack]
            exact sub_nonneg.mpr (hpotential i)
        | inr _ => simp [z]
  · funext row
    cases row with
    | inl i =>
        change
          Matrix.mulVec
              (analyticChargedPotentialBalance
                (fun _ => column) (fun _ => charge) 0) z i = 0
        rw [analyticChargedPotentialBalance_mulVec]
        have horiented :
            analyticChargedPotential
                (fun entry =>
                  match entry with
                  | Sum.inl coordinate => oriented coordinate
                  | Sum.inr (Sum.inl j) => slack j
                  | Sum.inr (Sum.inr _) => 1) =
              potential := by
          rw [show analyticChargedPotential
              (fun entry =>
                match entry with
                | Sum.inl coordinate => oriented coordinate
                | Sum.inr (Sum.inl j) => slack j
                | Sum.inr (Sum.inr _) => 1) =
              orientedFarkasToSigned oriented by rfl]
          simp [oriented]
        change
          (∑ destination,
              analyticChargedPotential z destination *
                column i destination) -
            slack i - charge i * 1 = 0
        rw [show analyticChargedPotential z = potential by
          simpa only [z] using horiented]
        dsimp only [slack]
        ring
    | inr u =>
        cases u
        change
          (∑ entry, analyticChargedPotentialScale entry * z entry) = 1
        rw [analyticChargedPotentialScale_dotProduct]

/-- Read a scaled charged-potential inequality from a scaled normalized
certificate. -/
theorem scaledChargedPotential_properties
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (charge : I → ℝ)
    {z : AnalyticChargedPotentialVariable S I → ℝ}
    {factor : ℝ}
    (hz_nonnegative : ∀ entry, 0 ≤ z entry)
    (hz_matrix :
      Matrix.mulVec
          (normalizedFarkasMatrix
            (analyticChargedPotentialBalance
              (fun _ => column) (fun _ => charge) 0)
            (analyticChargedPotentialScale :
              AnalyticChargedPotentialVariable S I → ℝ))
          z =
        factor • normalizedFarkasRhs) :
    ∀ i, factor * charge i ≤
      ∑ destination,
        analyticChargedPotential z destination * column i destination := by
  intro i
  have hi := congrFun hz_matrix (Sum.inl i)
  simp only [Matrix.mulVec, dotProduct, normalizedFarkasMatrix,
    normalizedFarkasRhs, Pi.smul_apply, smul_eq_mul, mul_zero] at hi
  change
    Matrix.mulVec
        (analyticChargedPotentialBalance
          (fun _ => column) (fun _ => charge) 0) z i = 0 at hi
  rw [analyticChargedPotentialBalance_mulVec] at hi
  have hscale := congrFun hz_matrix (Sum.inr ())
  simp only [Matrix.mulVec, dotProduct, normalizedFarkasMatrix,
    normalizedFarkasRhs, Pi.smul_apply, smul_eq_mul, mul_one] at hscale
  change
    (∑ entry, analyticChargedPotentialScale entry * z entry) =
      factor at hscale
  rw [analyticChargedPotentialScale_dotProduct] at hscale
  rw [hscale] at hi
  linarith [hz_nonnegative (Sum.inr (Sum.inl i))]

/-- Analyticity of the affine correction system. -/
theorem analytic_chargedPotentialBalance
    [DecidableEq I]
    (column : ℝ → I → S → ℝ) (charge : ℝ → I → ℝ)
    (hcolumn :
      ∀ i destination,
        AnalyticAt ℝ (fun t => column t i destination) 0)
    (hcharge : ∀ i, AnalyticAt ℝ (fun t => charge t i) 0) :
    ∀ i entry,
      AnalyticAt ℝ
        (fun t => analyticChargedPotentialBalance column charge t i entry)
        0 := by
  intro i entry
  cases entry with
  | inl oriented =>
      exact analyticAt_const.mul (hcolumn i oriented.1)
  | inr entry =>
      cases entry with
      | inl slack =>
          exact analyticAt_const
      | inr _ =>
          exact (hcharge i).neg

/-- Eventual charged-circulation feasibility yields a pole-cleared analytic
positive charged circulation. -/
theorem exists_analyticPositiveChargedCirculation_of_eventually
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (charge : ℝ → I → ℝ)
    (hcolumn :
      ∀ i destination,
        AnalyticAt ℝ (fun t => column t i destination) 0)
    (hcharge : ∀ i, AnalyticAt ℝ (fun t => charge t i) 0)
    (hfeasible :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        HasNormalizedPositiveChargedCirculation
          (column t) (charge t)) :
    Nonempty (AnalyticPositiveChargedCirculation column charge) := by
  classical
  let balance := analyticOccupationBalance column
  have hbalance :
      ∀ destination i,
        AnalyticAt ℝ (fun t => balance t destination i) 0 := by
    intro destination i
    exact hcolumn i destination
  have hnormalized :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (normalizedFarkasCertificateSet
          (balance t) (charge t)).Nonempty := by
    filter_upwards [hfeasible] with t ht
    obtain ⟨mass, hmass, hbalanceMass, hchargeMass⟩ := ht
    refine ⟨mass, hmass, ?_⟩
    funext row
    cases row with
    | inl destination =>
        simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
          Matrix.mulVec, dotProduct, balance,
          analyticOccupationBalance, mul_comm] using
            hbalanceMass destination
    | inr u =>
        cases u
        simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
          Matrix.mulVec, dotProduct, mul_comm] using hchargeMass
  obtain ⟨support, poleOrder, scaled, hscaledAnalytic, hscaled⟩ :=
    exists_analytic_scaled_eventual_feasible_normalizedFarkasCertificate
      balance charge hbalance hcharge hnormalized
  refine ⟨{
    poleOrder := poleOrder
    mass := scaled
    analytic_mass := hscaledAnalytic
    eventual := ?_
  }⟩
  filter_upwards [hscaled, self_mem_nhdsWithin] with t ht htpos
  have hpow : 0 ≤ t ^ poleOrder :=
    pow_nonneg (le_of_lt (mem_Ioi.mp htpos)) _
  have hscaledEq :
      t ^ poleOrder •
          supportCramerVector
            (normalizedFarkasMatrix (balance t) (charge t))
            normalizedFarkasRhs support =
        scaled t := by
    simpa using ht.1
  obtain ⟨hnonnegative, hmatrix⟩ :=
    scaled_normalizedFarkasCertificate_properties
      (balance t) (charge t) hpow hscaledEq ht.2
  refine ⟨hnonnegative, ?_, ?_⟩
  · intro destination
    have hrow := congrFun hmatrix (Sum.inl destination)
    simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
      Matrix.mulVec, dotProduct, balance,
      analyticOccupationBalance, mul_comm] using hrow
  · have hrow := congrFun hmatrix (Sum.inr ())
    simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
      Matrix.mulVec, dotProduct, mul_comm] using hrow

/-- Eventual failure of positive charged circulation yields a pole-cleared
analytic charged-occupation potential. -/
theorem exists_analyticScaledChargedOccupationPotential_of_eventually_not
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (charge : ℝ → I → ℝ)
    (hcolumn :
      ∀ i destination,
        AnalyticAt ℝ (fun t => column t i destination) 0)
    (hcharge : ∀ i, AnalyticAt ℝ (fun t => charge t i) 0)
    (hnot :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ¬HasNormalizedPositiveChargedCirculation
          (column t) (charge t)) :
    Nonempty
      (AnalyticScaledChargedOccupationPotential column charge) := by
  classical
  let balance :=
    analyticChargedPotentialBalance column charge
  let mass :
      AnalyticChargedPotentialVariable S I → ℝ :=
    analyticChargedPotentialScale
  have hbalance :
      ∀ i entry,
        AnalyticAt ℝ (fun t => balance t i entry) 0 := by
    exact analytic_chargedPotentialBalance
      column charge hcolumn hcharge
  have hmass :
      ∀ entry, AnalyticAt ℝ (fun _ : ℝ => mass entry) 0 :=
    fun _ => analyticAt_const
  have hfeasible :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (normalizedFarkasCertificateSet
          (balance t) mass).Nonempty := by
    filter_upwards [hnot] with t ht
    have halt :=
      normalizedPositiveChargedCirculation_xor_potential
        (column t) (charge t)
    rw [xor_def] at halt
    rcases halt with halt | halt
    · exact False.elim (ht halt.1)
    · exact
        normalizedFarkasCertificateSet_chargedPotential_nonempty
          (column t) (charge t) halt.1
  obtain ⟨support, poleOrder, scaled, hscaledAnalytic, hscaled⟩ :=
    exists_analytic_scaled_eventual_feasible_normalizedFarkasCertificate
      balance (fun _ => mass) hbalance hmass hfeasible
  let potential : ℝ → S → ℝ :=
    fun t => analyticChargedPotential (scaled t)
  have hpotentialAnalytic : AnalyticAt ℝ potential 0 := by
    rw [analyticAt_pi_iff]
    intro destination
    exact
      (analyticAt_pi_iff.mp hscaledAnalytic
          (Sum.inl (destination, true))).sub
        (analyticAt_pi_iff.mp hscaledAnalytic
          (Sum.inl (destination, false)))
  refine ⟨{
    poleOrder := poleOrder
    potential := potential
    analytic_potential := hpotentialAnalytic
    eventual := ?_
  }⟩
  filter_upwards [hscaled, self_mem_nhdsWithin] with t ht htpos
  have hpow : 0 ≤ t ^ poleOrder :=
    pow_nonneg (le_of_lt (mem_Ioi.mp htpos)) _
  have hscaledEq :
      t ^ poleOrder •
          supportCramerVector
            (normalizedFarkasMatrix (balance t) mass)
            normalizedFarkasRhs support =
        scaled t := by
    simpa using ht.1
  obtain ⟨hnonnegative, hmatrix⟩ :=
    scaled_normalizedFarkasCertificate_properties
      (balance t) mass hpow hscaledEq ht.2
  change
    Matrix.mulVec
        (normalizedFarkasMatrix
          (analyticChargedPotentialBalance
            (fun _ => column t) (fun _ => charge t) 0)
          analyticChargedPotentialScale)
        (scaled t) =
      t ^ poleOrder • normalizedFarkasRhs at hmatrix
  have hproperties :=
    scaledChargedPotential_properties
      (column t) (charge t) hnonnegative hmatrix
  simpa only [potential] using hproperties

/-- **Analytic charged occupation-flow alternative.**

Exactly one punctured branch occurs: a pole-cleared analytic positive charged
circulation, or a pole-cleared analytic charged-occupation potential. -/
theorem analyticPositiveChargedCirculation_xor_scaledPotential
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (charge : ℝ → I → ℝ)
    (hcolumn :
      ∀ i destination,
        AnalyticAt ℝ (fun t => column t i destination) 0)
    (hcharge : ∀ i, AnalyticAt ℝ (fun t => charge t i) 0) :
    Xor
      (Nonempty
        (AnalyticPositiveChargedCirculation column charge))
      (Nonempty
        (AnalyticScaledChargedOccupationPotential column charge)) := by
  classical
  let balance := analyticOccupationBalance column
  have hbalance :
      ∀ destination i,
        AnalyticAt ℝ (fun t => balance t destination i) 0 := by
    intro destination i
    exact hcolumn i destination
  rcases
      analytic_normalizedFarkas_feasibility_eventually_stabilizes
        balance charge hbalance hcharge with
    hfeasible | hnot
  · have hcharged :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          HasNormalizedPositiveChargedCirculation
            (column t) (charge t) := by
      filter_upwards [hfeasible] with t ht
      obtain ⟨mass, hmass, hmatrix⟩ := ht
      refine ⟨mass, hmass, ?_, ?_⟩
      · intro destination
        have hrow := congrFun hmatrix (Sum.inl destination)
        simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
          Matrix.mulVec, dotProduct, balance,
          analyticOccupationBalance, mul_comm] using hrow
      · have hrow := congrFun hmatrix (Sum.inr ())
        simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
          Matrix.mulVec, dotProduct, mul_comm] using hrow
    obtain ⟨C⟩ :=
      exists_analyticPositiveChargedCirculation_of_eventually
        column charge hcolumn hcharge hcharged
    refine Or.inl ⟨⟨C⟩, ?_⟩
    rintro ⟨P⟩
    obtain ⟨t, htcharged, htpotential⟩ :=
      (C.eventually_hasNormalizedPositiveChargedCirculation.and
        P.eventually_exists_chargedOccupationPotential).exists
    exact normalizedPositiveChargedCirculation_not_potential
      htcharged htpotential
  · have hchargedNot :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ¬HasNormalizedPositiveChargedCirculation
            (column t) (charge t) := by
      filter_upwards [hnot] with t ht
      intro hcharged
      apply ht
      obtain ⟨mass, hmass, hbalanceMass, hchargeMass⟩ := hcharged
      refine ⟨mass, hmass, ?_⟩
      funext row
      cases row with
      | inl destination =>
          simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
            Matrix.mulVec, dotProduct, balance,
            analyticOccupationBalance, mul_comm] using
              hbalanceMass destination
      | inr u =>
          cases u
          simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
            Matrix.mulVec, dotProduct, mul_comm] using hchargeMass
    obtain ⟨P⟩ :=
      exists_analyticScaledChargedOccupationPotential_of_eventually_not
        column charge hcolumn hcharge hchargedNot
    refine Or.inr ⟨⟨P⟩, ?_⟩
    rintro ⟨C⟩
    obtain ⟨t, htcharged, htnot⟩ :=
      (C.eventually_hasNormalizedPositiveChargedCirculation.and
        hchargedNot).exists
    exact htnot htcharged

end Probability
end Math
