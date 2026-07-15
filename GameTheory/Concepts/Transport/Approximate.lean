/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction.TotalVariation
import GameTheory.Concepts.Transport.Order

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
* `ApproxTransport.RelEquivalent` — extensional unit, associativity, and
  normalization laws across different error bounds
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

/-- Extensional equivalence of approximate realizations, ignoring their chosen
error bounds and comparing only the related profile-law pairs. -/
def RelEquivalent
    {VG VG' : ViewFamily G U Ω} {VH VH' : ViewFamily H U Ω}
    {ε δ : ℝ}
    (R : ApproxRealization G H VG VH ε)
    (S : ApproxRealization G H VG' VH' δ) : Prop :=
  R.rel = S.rel

/-- Identity realization has zero error. -/
noncomputable def refl (V : ViewFamily G U Ω) :
    ApproxRealization G G V V 0 where
  rel := Eq
  error_nonneg := le_rfl
  law_le := by
    intro μG μH hrel u
    subst μH
    exact le_of_eq (pmfTV_self (V.claw u μG))

/-- Approximate realizations compose and their errors add. -/
noncomputable def comp {K : GameForm ι}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {VK : ViewFamily K U Ω} {ε δ : ℝ}
    (RGH : ApproxRealization G H VG VH ε)
    (RHK : ApproxRealization H K VH VK δ) :
    ApproxRealization G K VG VK (ε + δ) where
  rel := fun μG μK => ∃ μH, RGH.rel μG μH ∧ RHK.rel μH μK
  error_nonneg := add_nonneg RGH.error_nonneg RHK.error_nonneg
  law_le := by
    rintro μG μK ⟨μH, hGH, hHK⟩ u
    exact le_trans
      (pmfTV_triangle (VG.claw u μG) (VH.claw u μH) (VK.claw u μK))
      (add_le_add (RGH.law_le hGH u) (RHK.law_le hHK u))

@[simp] theorem comp_rel {K : GameForm ι}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {VK : ViewFamily K U Ω} {ε δ : ℝ}
    (RGH : ApproxRealization G H VG VH ε)
    (RHK : ApproxRealization H K VH VK δ)
    (μG : PMF G.Profile) (μK : PMF K.Profile) :
    (RGH.comp RHK).rel μG μK ↔
      ∃ μH, RGH.rel μG μH ∧ RHK.rel μH μK :=
  Iff.rfl

theorem refl_comp {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ε : ℝ} (R : ApproxRealization G H VG VH ε) :
    (refl VG).comp R |>.RelEquivalent R := by
  funext μG μH
  apply propext
  constructor
  · rintro ⟨μG', rfl, h⟩
    exact h
  · intro h
    exact ⟨μG, rfl, h⟩

theorem comp_refl {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ε : ℝ} (R : ApproxRealization G H VG VH ε) :
    R.comp (refl VH) |>.RelEquivalent R := by
  funext μG μH
  apply propext
  constructor
  · rintro ⟨μH', h, rfl⟩
    exact h
  · intro h
    exact ⟨μH, h, rfl⟩

theorem comp_assoc {K L : GameForm ι}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {VK : ViewFamily K U Ω} {VL : ViewFamily L U Ω}
    {ε δ ζ : ℝ}
    (RGH : ApproxRealization G H VG VH ε)
    (RHK : ApproxRealization H K VH VK δ)
    (RKL : ApproxRealization K L VK VL ζ) :
    (RGH.comp RHK).comp RKL |>.RelEquivalent
      (RGH.comp (RHK.comp RKL)) := by
  funext μG μL
  apply propext
  constructor
  · rintro ⟨μK, ⟨μH, hGH, hHK⟩, hKL⟩
    exact ⟨μH, hGH, μK, hHK, hKL⟩
  · rintro ⟨μH, hGH, μK, hHK, hKL⟩
    exact ⟨μK, ⟨μH, hGH, hHK⟩, hKL⟩

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

theorem garble_id {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {ε : ℝ}
    (R : ApproxRealization G H VG VH ε) :
    (R.garble (fun _ => _root_.id)).RelEquivalent R :=
  rfl

theorem garble_comp {Ω' Ω'' : U → Type}
    [∀ u, Fintype (Ω' u)] [∀ u, Fintype (Ω'' u)]
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {ε : ℝ}
    (R : ApproxRealization G H VG VH ε)
    (g : ∀ u, Ω u → Ω' u) (h : ∀ u, Ω' u → Ω'' u) :
    ((R.garble g).garble h).RelEquivalent
      (R.garble (fun u => h u ∘ g u)) :=
  rfl

theorem comp_garble {K : GameForm ι} {Ω' : U → Type}
    [∀ u, Fintype (Ω' u)]
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {VK : ViewFamily K U Ω} {ε δ : ℝ}
    (RGH : ApproxRealization G H VG VH ε)
    (RHK : ApproxRealization H K VH VK δ)
    (g : ∀ u, Ω u → Ω' u) :
    ((RGH.comp RHK).garble g).RelEquivalent
      ((RGH.garble g).comp (RHK.garble g)) :=
  rfl

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

/-- Extensional equivalence of approximate transports, comparing only their
profile-law relations across possibly different error bounds. -/
def RelEquivalent
    {VG VG' : ViewFamily G U Ω} {VH VH' : ViewFamily H U Ω}
    {ΔG ΔG' : DeviationFamily G U} {ΔH ΔH' : DeviationFamily H U}
    {ε δ : ℝ}
    (T : ApproxTransport G H VG VH ΔG ΔH ε)
    (S : ApproxTransport G H VG' VH' ΔG' ΔH' δ) : Prop :=
  T.rel = S.rel

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
  toApproxRealization := TGH.toApproxRealization.comp THK.toApproxRealization
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

@[simp] theorem comp_rel {VK : ViewFamily K U Ω}
    {ΔK : DeviationFamily K U} {ε δ : ℝ}
    (TGH : ApproxTransport G H VG VH ΔG ΔH ε)
    (THK : ApproxTransport H K VH VK ΔH ΔK δ)
    (μG : PMF G.Profile) (μK : PMF K.Profile) :
    (TGH.comp THK).rel μG μK ↔
      ∃ μH, TGH.rel μG μH ∧ THK.rel μH μK :=
  Iff.rfl

theorem refl_comp {ε : ℝ}
    (T : ApproxTransport G H VG VH ΔG ΔH ε) :
    (refl VG ΔG).comp T |>.RelEquivalent T :=
  ApproxRealization.refl_comp T.toApproxRealization

theorem comp_refl {ε : ℝ}
    (T : ApproxTransport G H VG VH ΔG ΔH ε) :
    T.comp (refl VH ΔH) |>.RelEquivalent T :=
  ApproxRealization.comp_refl T.toApproxRealization

theorem comp_assoc {L : GameForm ι}
    {VK : ViewFamily K U Ω} {VL : ViewFamily L U Ω}
    {ΔK : DeviationFamily K U} {ΔL : DeviationFamily L U}
    {ε δ ζ : ℝ}
    (TGH : ApproxTransport G H VG VH ΔG ΔH ε)
    (THK : ApproxTransport H K VH VK ΔH ΔK δ)
    (TKL : ApproxTransport K L VK VL ΔK ΔL ζ) :
    (TGH.comp THK).comp TKL |>.RelEquivalent
      (TGH.comp (THK.comp TKL)) :=
  ApproxRealization.comp_assoc TGH.toApproxRealization
    THK.toApproxRealization TKL.toApproxRealization

theorem mono_relEquivalent {ε δ : ℝ}
    (T : ApproxTransport G H VG VH ΔG ΔH ε) (hεδ : ε ≤ δ) :
    (T.mono hεδ).RelEquivalent T :=
  rfl

theorem garble_id {ε : ℝ}
    (T : ApproxTransport G H VG VH ΔG ΔH ε) :
    (T.garble (fun _ => _root_.id)).RelEquivalent T :=
  ApproxRealization.garble_id T.toApproxRealization

theorem garble_comp {Ω' Ω'' : U → Type}
    [∀ u, Fintype (Ω' u)] [∀ u, Fintype (Ω'' u)]
    {ε : ℝ} (T : ApproxTransport G H VG VH ΔG ΔH ε)
    (g : ∀ u, Ω u → Ω' u) (h : ∀ u, Ω' u → Ω'' u) :
    ((T.garble g).garble h).RelEquivalent
      (T.garble (fun u => h u ∘ g u)) :=
  ApproxRealization.garble_comp T.toApproxRealization g h

theorem comp_garble {Ω' : U → Type} [∀ u, Fintype (Ω' u)]
    {VK : ViewFamily K U Ω} {ΔK : DeviationFamily K U}
    {ε δ : ℝ}
    (TGH : ApproxTransport G H VG VH ΔG ΔH ε)
    (THK : ApproxTransport H K VH VK ΔH ΔK δ)
    (g : ∀ u, Ω u → Ω' u) :
    ((TGH.comp THK).garble g).RelEquivalent
      ((TGH.garble g).comp (THK.garble g)) :=
  ApproxRealization.comp_garble TGH.toApproxRealization
    THK.toApproxRealization g

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

namespace Transport

theorem toApprox_refl {G : GameForm ι} {U : Type} {Ω : U → Type}
    [∀ u, Fintype (Ω u)]
    (V : ViewFamily G U Ω) (Δ : DeviationFamily G U) :
    (Transport.refl V Δ).toApprox.RelEquivalent (ApproxTransport.refl V Δ) :=
  rfl

theorem toApprox_comp {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    [∀ u, Fintype (Ω u)]
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {VK : ViewFamily K U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    {ΔK : DeviationFamily K U}
    (TGH : Transport G H VG VH ΔG ΔH)
    (THK : Transport H K VH VK ΔH ΔK) :
    (TGH.compSameMiddle THK).toApprox.RelEquivalent
      (TGH.toApprox.comp THK.toApprox) :=
  rfl

theorem toApprox_garble {G H : GameForm ι} {U : Type}
    {Ω Ω' : U → Type} [∀ u, Fintype (Ω u)] [∀ u, Fintype (Ω' u)]
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (T : Transport G H VG VH ΔG ΔH) (g : ∀ u, Ω u → Ω' u) :
    (T.garble g).toApprox.RelEquivalent (T.toApprox.garble g) :=
  rfl

end Transport

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
