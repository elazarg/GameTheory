/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction.TotalVariation
import GameTheory.Concepts.Transport.Simulation

/-!
# Approximate Law Transport

Quantitative analogues of law-preserving realizations and transports. Exact
equality of observed laws is replaced by a finite-law total-variation bound.
The base-profile and deviation bounds use the same error parameter, so errors
add transparently under composition.

The final section turns approximate law transport into approximate equilibrium
transport for bounded observation utilities.

## Main definitions

* `GameForm.ApproxRealization` — related profiles have nearby observed laws
* `GameForm.ApproxTransport` — target deviations admit nearby source matches
* `GameForm.approxExpectedPref` — expected-utility preference with additive slack

## Main results

* `ApproxTransport.comp` — approximate transports compose and their errors add
* `ApproxTransport.garble` — deterministic observation loses no accuracy
* `Transport.toApprox` — every exact transport has zero error
* `ApproxTransport.target_eq_of_source_eq` — bounded-utility approximate
  equilibrium transfer
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- A relation between profile laws whose observed laws are within `ε` in total
variation for every deviating unit. -/
structure ApproxRealization (G H : GameForm ι) {U : Type} {Ω : U → Type}
    [∀ u, Fintype (Ω u)]
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (ε : ℝ) where
  /-- Which source profile laws correspond to which target profile laws. -/
  rel : PMF G.Profile → PMF H.Profile → Prop
  /-- Approximation errors are nonnegative. -/
  error_nonneg : 0 ≤ ε
  /-- Related profiles induce nearby observed laws. -/
  law_le : ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, rel μG μH →
    ∀ u, pmfTV (VG.claw u μG) (VH.claw u μH) ≤ ε

namespace ApproxRealization

variable {G H : GameForm ι} {U : Type} {Ω : U → Type}
variable [∀ u, Fintype (Ω u)]

/-- Identity realization has zero error. -/
noncomputable def refl (V : ViewFamily G U Ω) :
    ApproxRealization G G V V 0 where
  rel := Eq
  error_nonneg := le_rfl
  law_le := by
    intro μG μH hrel u
    subst μH
    exact le_of_eq (pmfTV_self (V.claw u μG))

/-- Deterministic coarsening of observations cannot increase realization error. -/
noncomputable def garble {Ω' : U → Type} [∀ u, Fintype (Ω' u)]
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {ε : ℝ}
    (R : ApproxRealization G H VG VH ε) (g : ∀ u, Ω u → Ω' u) :
    ApproxRealization G H (VG.garble g) (VH.garble g) ε where
  rel := R.rel
  error_nonneg := R.error_nonneg
  law_le := by
    intro μG μH hrel u
    rw [ViewFamily.claw_garble, ViewFamily.claw_garble]
    exact le_trans (pmfTV_map_le (g u) (VG.claw u μG) (VH.claw u μH))
      (R.law_le hrel u)

end ApproxRealization

/-- An approximate realization together with a backtranslation of every target
deviation to a source deviation whose observed law is also within `ε`. -/
structure ApproxTransport (G H : GameForm ι) {U : Type} {Ω : U → Type}
    [∀ u, Fintype (Ω u)]
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω)
    (ΔG : DeviationFamily G U) (ΔH : DeviationFamily H U) (ε : ℝ)
    extends ApproxRealization G H VG VH ε where
  /-- Approximate deviation backtranslation. -/
  simulate : ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, rel μG μH →
    ∀ u (dH : ΔH.Dev u), ∃ dG : ΔG.Dev u,
      pmfTV (VG.claw u (ΔG.deviate μG u dG))
        (VH.claw u (ΔH.deviate μH u dH)) ≤ ε

namespace ApproxTransport

variable {G H K : GameForm ι} {U : Type} {Ω : U → Type}
variable [∀ u, Fintype (Ω u)]
variable {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
variable {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}

/-- Identity transport has zero error. -/
noncomputable def refl (V : ViewFamily G U Ω) (Δ : DeviationFamily G U) :
    ApproxTransport G G V V Δ Δ 0 where
  toApproxRealization := ApproxRealization.refl V
  simulate := by
    intro μG μH hrel u dH
    subst μH
    exact ⟨dH, le_of_eq (pmfTV_self _)⟩

/-- Any larger error bound also validates an approximate transport. -/
noncomputable def mono {ε δ : ℝ}
    (T : ApproxTransport G H VG VH ΔG ΔH ε) (hεδ : ε ≤ δ) :
    ApproxTransport G H VG VH ΔG ΔH δ where
  rel := T.rel
  error_nonneg := le_trans T.error_nonneg hεδ
  law_le := fun hrel u => le_trans (T.law_le hrel u) hεδ
  simulate := by
    intro μG μH hrel u dH
    obtain ⟨dG, hd⟩ := T.simulate hrel u dH
    exact ⟨dG, le_trans hd hεδ⟩

/-- Deterministic coarsening of observations cannot increase transport error. -/
noncomputable def garble {Ω' : U → Type} [∀ u, Fintype (Ω' u)]
    {ε : ℝ} (T : ApproxTransport G H VG VH ΔG ΔH ε)
    (g : ∀ u, Ω u → Ω' u) :
    ApproxTransport G H (VG.garble g) (VH.garble g) ΔG ΔH ε where
  toApproxRealization := T.toApproxRealization.garble g
  simulate := by
    intro μG μH hrel u dH
    obtain ⟨dG, hd⟩ := T.simulate hrel u dH
    refine ⟨dG, ?_⟩
    rw [ViewFamily.claw_garble, ViewFamily.claw_garble]
    exact le_trans
      (pmfTV_map_le (g u)
        (VG.claw u (ΔG.deviate μG u dG))
        (VH.claw u (ΔH.deviate μH u dH)))
      hd

/-- Approximate transports compose; their total-variation errors add. -/
noncomputable def comp {VK : ViewFamily K U Ω}
    {ΔK : DeviationFamily K U} {ε δ : ℝ}
    (TGH : ApproxTransport G H VG VH ΔG ΔH ε)
    (THK : ApproxTransport H K VH VK ΔH ΔK δ) :
    ApproxTransport G K VG VK ΔG ΔK (ε + δ) where
  rel := fun μG μK => ∃ μH, TGH.rel μG μH ∧ THK.rel μH μK
  error_nonneg := add_nonneg TGH.error_nonneg THK.error_nonneg
  law_le := by
    rintro μG μK ⟨μH, hGH, hHK⟩ u
    exact le_trans
      (pmfTV_triangle (VG.claw u μG) (VH.claw u μH) (VK.claw u μK))
      (add_le_add (TGH.law_le hGH u) (THK.law_le hHK u))
  simulate := by
    rintro μG μK ⟨μH, hGH, hHK⟩ u dK
    obtain ⟨dH, hdHK⟩ := THK.simulate hHK u dK
    obtain ⟨dG, hdGH⟩ := TGH.simulate hGH u dH
    refine ⟨dG, ?_⟩
    exact le_trans
      (pmfTV_triangle
        (VG.claw u (ΔG.deviate μG u dG))
        (VH.claw u (ΔH.deviate μH u dH))
        (VK.claw u (ΔK.deviate μK u dK)))
      (add_le_add hdGH hdHK)

end ApproxTransport

/-- Every exact law transport is an approximate transport with zero error. -/
noncomputable def Transport.toApprox {G H : GameForm ι} {U : Type}
    {Ω : U → Type} [∀ u, Fintype (Ω u)]
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (T : Transport G H VG VH ΔG ΔH) :
    ApproxTransport G H VG VH ΔG ΔH 0 where
  rel := T.rel
  error_nonneg := le_rfl
  law_le := by
    intro μG μH hrel u
    rw [T.law_eq hrel u]
    exact le_of_eq (pmfTV_self _)
  simulate := by
    intro μG μH hrel u dH
    obtain ⟨dG, hd⟩ := T.simulate hrel u dH
    refine ⟨dG, ?_⟩
    rw [hd]
    exact le_of_eq (pmfTV_self _)

/-- Expected-utility preference on observed laws with unit-dependent additive
slack. `approxExpectedPref payoff η u old new` says the deviation from `old` to
`new` gains at most `η u`. -/
noncomputable def approxExpectedPref {U : Type} {Ω : U → Type}
    (payoff : ∀ u, Ω u → ℝ) (η : U → ℝ) :
    ∀ u, PMF (Ω u) → PMF (Ω u) → Prop :=
  fun u old new => expect old (payoff u) + η u ≥ expect new (payoff u)

namespace ApproxTransport

/-- Bounded-utility approximate equilibrium transfer. If both status-quo and
matched deviation laws are within `ε`, an `η`-equilibrium in the source becomes
an `η + 2 (upper - lower) ε`-equilibrium in the target. -/
theorem target_eq_of_source_eq {G H : GameForm ι} {U : Type}
    {Ω : U → Type} [∀ u, Fintype (Ω u)]
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U} {ε : ℝ}
    (T : ApproxTransport G H VG VH ΔG ΔH ε)
    (payoff : ∀ u, Ω u → ℝ) (lower upper η : U → ℝ)
    (hlower : ∀ u ω, lower u ≤ payoff u ω)
    (hupper : ∀ u ω, payoff u ω ≤ upper u)
    (hlu : ∀ u, lower u ≤ upper u)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : T.rel μG μH)
    (hEq : G.IsDeviationEqFor
      (observedPref VG (approxExpectedPref payoff η)) μG ΔG) :
    H.IsDeviationEqFor
      (observedPref VH (approxExpectedPref payoff
        (fun u => η u + 2 * (upper u - lower u) * ε))) μH ΔH := by
  intro u dH
  obtain ⟨dG, hdevTV⟩ := T.simulate hrel u dH
  have hsrc := hEq u dG
  change expect (VG.claw u μG) (payoff u) + η u ≥
    expect (VG.claw u (ΔG.deviate μG u dG)) (payoff u) at hsrc
  change expect (VH.claw u μH) (payoff u) +
      (η u + 2 * (upper u - lower u) * ε) ≥
    expect (VH.claw u (ΔH.deviate μH u dH)) (payoff u)
  have hbase := abs_expect_sub_le_range_mul_pmfTV
    (VG.claw u μG) (VH.claw u μH) (payoff u)
    (hlower u) (hupper u)
  have hdev := abs_expect_sub_le_range_mul_pmfTV
    (VG.claw u (ΔG.deviate μG u dG))
    (VH.claw u (ΔH.deviate μH u dH)) (payoff u)
    (hlower u) (hupper u)
  have hrange : 0 ≤ upper u - lower u := sub_nonneg.mpr (hlu u)
  have hbase' :
      |expect (VG.claw u μG) (payoff u) -
        expect (VH.claw u μH) (payoff u)| ≤
          (upper u - lower u) * ε :=
    le_trans hbase (mul_le_mul_of_nonneg_left (T.law_le hrel u) hrange)
  have hdev' :
      |expect (VG.claw u (ΔG.deviate μG u dG)) (payoff u) -
        expect (VH.claw u (ΔH.deviate μH u dH)) (payoff u)| ≤
          (upper u - lower u) * ε :=
    le_trans hdev (mul_le_mul_of_nonneg_left hdevTV hrange)
  rw [abs_le] at hbase' hdev'
  rcases hbase' with ⟨_hbaseUpper, hbaseLower⟩
  rcases hdev' with ⟨hdevUpper, _hdevLower⟩
  linarith

/-- Uniform-bound specialization of `target_eq_of_source_eq`: a scalar
`η`-equilibrium transfers with slack `η + 2 (upper - lower) ε`. -/
theorem target_eq_of_source_eq_uniform {G H : GameForm ι} {U : Type}
    {Ω : U → Type} [∀ u, Fintype (Ω u)]
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U} {ε : ℝ}
    (T : ApproxTransport G H VG VH ΔG ΔH ε)
    (payoff : ∀ u, Ω u → ℝ) (lower upper η : ℝ)
    (hlower : ∀ u ω, lower ≤ payoff u ω)
    (hupper : ∀ u ω, payoff u ω ≤ upper) (hlu : lower ≤ upper)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : T.rel μG μH)
    (hEq : G.IsDeviationEqFor
      (observedPref VG (approxExpectedPref payoff (fun _ => η))) μG ΔG) :
    H.IsDeviationEqFor
      (observedPref VH (approxExpectedPref payoff
        (fun _ => η + 2 * (upper - lower) * ε))) μH ΔH := by
  exact T.target_eq_of_source_eq payoff (fun _ => lower) (fun _ => upper)
    (fun _ => η) hlower hupper (fun _ => hlu) hrel hEq

end ApproxTransport

end GameForm
end GameTheory
