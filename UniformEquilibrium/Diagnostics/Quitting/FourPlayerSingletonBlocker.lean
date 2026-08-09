/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSurplus

/-!
# A four-player singleton packet with no complementary distribution

This module records an exact rational finite regression for the distinction
between a normalized singleton source packet and a complementary singleton
mixture.  The diagonal reward is one and the displayed excess matrix is the
integer blocker matrix scaled by one third, so every singleton reward lies in
`[0, 2]`.  Uniform owner mass strictly overdelivers every pinned diagonal
target, while no probability distribution can make every positive-mass row
complementary.

Only the singleton reward table is asserted here.  In particular, this is not
a quitting-game counterexample: nonsingleton collision rewards, exact product
root dynamics, punishment-floor capacity, and late-window realization are
additional data that this finite regression does not supply.
-/

noncomputable section

namespace GameTheory
namespace FourPlayerSingletonBlocker

private theorem fin4_succ_two_eq_three :
    Fin.succ (2 : Fin 3) = (3 : Fin 4) := by
  decide

private theorem vec4_apply_two (a b c d : ℝ) :
    ![a, b, c, d] (2 : Fin 4) = c := by
  rw [show (2 : Fin 4) = Fin.succ (Fin.succ (0 : Fin 2)) by decide]
  rfl

private theorem vec4_apply_three (a b c d : ℝ) :
    ![a, b, c, d] (3 : Fin 4) = d := by
  rw [show (3 : Fin 4) =
    Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))) by decide]
  rfl

/-- The normalized singleton-excess matrix from the four-player blocker.
Rows are payoff coordinates and columns are singleton exit owners. -/
def excess : Fin 4 → Fin 4 → ℝ :=
  ![![0, -(1 / 3), 2 / 3, 2 / 3],
    ![2 / 3, 0, 1, -1],
    ![-(1 / 3), 2 / 3, 0, 1],
    ![1, 2 / 3, -(2 / 3), 0]]

/-- The corresponding bounded singleton reward table, with diagonal target
one. -/
def singletonReward (who owner : Fin 4) : ℝ := 1 + excess who owner

/-- Uniform normalized singleton owner mass. -/
def uniformMass (_owner : Fin 4) : ℝ := 1 / 4

/-- Excess delivered to one payoff row by an owner distribution. -/
def rowExcess (mass : Fin 4 → ℝ) (who : Fin 4) : ℝ :=
  ∑ owner, mass owner * excess who owner

theorem rowExcess_eq_vector (mass : Fin 4 → ℝ) :
    rowExcess mass =
      ![-(mass 1) / 3 + 2 * mass 2 / 3 + 2 * mass 3 / 3,
        2 * mass 0 / 3 + mass 2 - mass 3,
        -(mass 0) / 3 + 2 * mass 1 / 3 + mass 3,
        mass 0 + 2 * mass 1 / 3 - 2 * mass 2 / 3] := by
  funext who
  fin_cases who <;>
    norm_num [rowExcess, excess, Fin.sum_univ_succ,
      fin4_succ_two_eq_three] <;> ring

theorem sum_mass_eq (mass : Fin 4 → ℝ) :
    ∑ owner, mass owner = mass 0 + mass 1 + mass 2 + mass 3 := by
  norm_num [Fin.sum_univ_succ, fin4_succ_two_eq_three]
  ring

theorem singletonReward_mem_Icc (who owner : Fin 4) :
    singletonReward who owner ∈ Set.Icc (0 : ℝ) 2 := by
  fin_cases who <;> fin_cases owner <;>
    norm_num [singletonReward, excess]

theorem singletonReward_diagonal (who : Fin 4) :
    singletonReward who who = 1 := by
  fin_cases who <;> norm_num [singletonReward, excess]

theorem uniformMass_nonneg (owner : Fin 4) :
    0 ≤ uniformMass owner := by
  norm_num [uniformMass]

theorem uniformMass_sum : ∑ owner, uniformMass owner = 1 := by
  norm_num [uniformMass, Fin.sum_univ_succ]

/-- The uniform source packet strictly overdelivers every pinned diagonal
target. -/
theorem uniform_rowExcess_pos (who : Fin 4) :
    0 < rowExcess uniformMass who := by
  fin_cases who <;>
    norm_num [rowExcess, uniformMass, excess, Fin.sum_univ_succ]

theorem uniform_singletonDelivery_gt_diagonal (who : Fin 4) :
    1 < ∑ owner, uniformMass owner * singletonReward who owner := by
  have hrow := uniform_rowExcess_pos who
  calc
    1 < 1 + rowExcess uniformMass who := by linarith
    _ = ∑ owner, uniformMass owner * singletonReward who owner := by
      unfold rowExcess singletonReward
      simp_rw [mul_add, mul_one]
      rw [Finset.sum_add_distrib, uniformMass_sum]

/-- **Exact no-complementarity regression.**  No nonnegative normalized mass
with nonnegative row excess can have zero excess on every positive-mass row.
Pure singleton masses satisfy their sole active-row equality but fail a
spectator row, which is why the global row-nonnegativity hypothesis is
essential. -/
theorem no_complementary_probability
    (mass : Fin 4 → ℝ) (hmass : ∀ owner, 0 ≤ mass owner)
    (hsum : ∑ owner, mass owner = 1)
    (hrow : ∀ who, 0 ≤ rowExcess mass who) :
    ¬ ∀ who, 0 < mass who → rowExcess mass who = 0 := by
  intro hcomp
  have hr0 := hrow (0 : Fin 4)
  have hr1 := hrow (1 : Fin 4)
  have hr2 := hrow (2 : Fin 4)
  have hr3 := hrow (3 : Fin 4)
  have h0 : mass 0 = 0 ∨ rowExcess mass 0 = 0 := by
    by_cases hz : mass 0 = 0
    · exact Or.inl hz
    · exact Or.inr (hcomp 0 (lt_of_le_of_ne (hmass 0) (Ne.symm hz)))
  have h1 : mass 1 = 0 ∨ rowExcess mass 1 = 0 := by
    by_cases hz : mass 1 = 0
    · exact Or.inl hz
    · exact Or.inr (hcomp 1 (lt_of_le_of_ne (hmass 1) (Ne.symm hz)))
  have h2 : mass 2 = 0 ∨ rowExcess mass 2 = 0 := by
    by_cases hz : mass 2 = 0
    · exact Or.inl hz
    · exact Or.inr (hcomp 2 (lt_of_le_of_ne (hmass 2) (Ne.symm hz)))
  have h3 : mass 3 = 0 ∨ rowExcess mass 3 = 0 := by
    by_cases hz : mass 3 = 0
    · exact Or.inl hz
    · exact Or.inr (hcomp 3 (lt_of_le_of_ne (hmass 3) (Ne.symm hz)))
  rw [sum_mass_eq] at hsum
  rw [congrFun (rowExcess_eq_vector mass) 0] at h0
  rw [congrFun (rowExcess_eq_vector mass) 1] at h1
  rw [congrFun (rowExcess_eq_vector mass) 2] at h2
  rw [congrFun (rowExcess_eq_vector mass) 3] at h3
  rw [congrFun (rowExcess_eq_vector mass) 0] at hr0
  rw [congrFun (rowExcess_eq_vector mass) 1] at hr1
  rw [congrFun (rowExcess_eq_vector mass) 2] at hr2
  rw [congrFun (rowExcess_eq_vector mass) 3] at hr3
  simp only [vec4_apply_two, vec4_apply_three] at h0 h1 h2 h3
  simp only [vec4_apply_two, vec4_apply_three] at hr0 hr1 hr2 hr3
  norm_num [fin4_succ_two_eq_three] at h0 h1 h2 h3 hr0 hr1 hr2 hr3
  rcases h0 with h0 | h0
  <;> rcases h1 with h1 | h1
  <;> rcases h2 with h2 | h2
  <;> rcases h3 with h3 | h3
  <;> linarith

/-- Consequently every probability distribution has a positive-mass owner
with nonzero singleton excess. -/
theorem exists_active_nonzero_excess
    (mass : Fin 4 → ℝ) (hmass : ∀ owner, 0 ≤ mass owner)
    (hsum : ∑ owner, mass owner = 1)
    (hrow : ∀ who, 0 ≤ rowExcess mass who) :
    ∃ who, 0 < mass who ∧ rowExcess mass who ≠ 0 := by
  by_contra h
  push Not at h
  exact no_complementary_probability mass hmass hsum hrow h

/-! ## Robust escape separation -/

/-- The probability simplex of singleton owner distributions. -/
def probabilitySimplex : Set (Fin 4 → ℝ) :=
  {mass | (∀ owner, 0 ≤ mass owner) ∧ ∑ owner, mass owner = 1}

/-- Promise-or-refusal escape defect.  A negative row creates a promise
escape; positive excess at a positive-mass owner creates a refusal escape. -/
def escapeDefect (mass : Fin 4 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who =>
    max (max 0 (-rowExcess mass who))
      (max 0 (mass who * rowExcess mass who))

theorem escapeDefect_pos_of_mem_probabilitySimplex
    {mass : Fin 4 → ℝ} (hmass : mass ∈ probabilitySimplex) :
    0 < escapeDefect mass := by
  rcases hmass with ⟨hmassNonneg, hmassSum⟩
  by_contra hnot
  have hdefect : escapeDefect mass ≤ 0 := le_of_not_gt hnot
  have hcomponent : ∀ who,
      max (max 0 (-rowExcess mass who))
          (max 0 (mass who * rowExcess mass who)) ≤ 0 := by
    intro who
    exact (Finset.le_sup'
      (fun who => max (max 0 (-rowExcess mass who))
        (max 0 (mass who * rowExcess mass who)))
      (Finset.mem_univ who)).trans hdefect
  have hrow : ∀ who, 0 ≤ rowExcess mass who := by
    intro who
    have hpromise := (le_max_left
      (max 0 (-rowExcess mass who))
      (max 0 (mass who * rowExcess mass who))).trans (hcomponent who)
    have hnegative := (le_max_right 0 (-rowExcess mass who)).trans hpromise
    linarith
  have hcomp : ∀ who, 0 < mass who → rowExcess mass who = 0 := by
    intro who hwho
    have hrefusal := (le_max_right
      (max 0 (-rowExcess mass who))
      (max 0 (mass who * rowExcess mass who))).trans (hcomponent who)
    have hproduct :=
      (le_max_right 0 (mass who * rowExcess mass who)).trans hrefusal
    nlinarith [hrow who]
  exact no_complementary_probability mass hmassNonneg hmassSum hrow hcomp

theorem continuous_rowExcess (who : Fin 4) :
    Continuous (fun mass : Fin 4 → ℝ => rowExcess mass who) := by
  unfold rowExcess
  apply continuous_finsetSum
  intro owner _
  exact (continuous_apply owner).mul continuous_const

theorem continuous_escapeDefect : Continuous escapeDefect := by
  unfold escapeDefect
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro who _
  exact (continuous_const.max (continuous_rowExcess who).neg).max
    (continuous_const.max
      ((continuous_apply who).mul (continuous_rowExcess who)))

theorem isClosed_probabilitySimplex : IsClosed probabilitySimplex := by
  have hnonneg : IsClosed {mass : Fin 4 → ℝ | ∀ owner, 0 ≤ mass owner} := by
    rw [show {mass : Fin 4 → ℝ | ∀ owner, 0 ≤ mass owner} =
        ⋂ owner, {mass | mass owner ∈ Set.Ici (0 : ℝ)} by
      ext mass
      simp]
    exact isClosed_iInter fun owner =>
      isClosed_Ici.preimage (continuous_apply owner)
  have hsumContinuous : Continuous (fun mass : Fin 4 → ℝ => ∑ owner, mass owner) := by
    exact continuous_finsetSum _ fun owner _ => continuous_apply owner
  have hsum : IsClosed {mass : Fin 4 → ℝ | ∑ owner, mass owner = 1} :=
    isClosed_singleton.preimage hsumContinuous
  rw [show probabilitySimplex =
      {mass : Fin 4 → ℝ | ∀ owner, 0 ≤ mass owner} ∩
        {mass : Fin 4 → ℝ | ∑ owner, mass owner = 1} by
    ext mass
    rfl]
  exact hnonneg.inter hsum

theorem isCompact_probabilitySimplex : IsCompact probabilitySimplex := by
  apply (isCompact_Icc : IsCompact
    (Set.Icc (0 : Fin 4 → ℝ) (1 : Fin 4 → ℝ))).of_isClosed_subset
      isClosed_probabilitySimplex
  intro mass hmass
  rcases hmass with ⟨hmassNonneg, hmassSum⟩
  constructor
  · exact hmassNonneg
  · intro owner
    change mass owner ≤ (1 : ℝ)
    rw [← hmassSum]
    exact Finset.single_le_sum
      (fun other _ => hmassNonneg other) (Finset.mem_univ owner)

theorem probabilitySimplex_nonempty : probabilitySimplex.Nonempty := by
  refine ⟨uniformMass, ?_⟩
  exact ⟨uniformMass_nonneg, uniformMass_sum⟩

/-- **Uniform robust blocker separation.**  The exact escape defect has a
strictly positive lower bound on the singleton probability simplex.  This is
the finite compactness margin available to absorb sufficiently small
collision and ordering perturbations; it does not itself provide the
late-window approximation. -/
theorem exists_pos_uniform_escapeSeparation :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ mass ∈ probabilitySimplex, δ ≤ escapeDefect mass := by
  obtain ⟨mass, hmass, hmin⟩ :=
    isCompact_probabilitySimplex.exists_isMinOn
      probabilitySimplex_nonempty continuous_escapeDefect.continuousOn
  exact ⟨escapeDefect mass,
    escapeDefect_pos_of_mem_probabilitySimplex hmass,
    fun other hother => hmin hother⟩

end FourPlayerSingletonBlocker
end GameTheory
