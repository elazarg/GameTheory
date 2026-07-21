/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Repeated.MonitoringPublicRandomization

/-!
# Fixed Public Draws under Public Monitoring

A fixed public draw device supplies a seed before initial play and independently
samples the seed for the next period together with each post-action monitoring
signal. Thus a period's seed is observed before that period's action, while the
base monitoring signal retains its original post-action timing and marginal
law.

This module handles a fixed seed type and law. It does not claim that one such
device realizes every history-dependent finite lottery appearing in an
abstract convexified APS operator.
-/

noncomputable section

namespace GameTheory

namespace KernelGame

namespace PublicMonitoring

variable {ι : Type} {G : KernelGame ι}

/-- Add an independent draw for the next period to every public monitoring
signal. The first component is the next public seed; the second is the original
post-action signal. -/
def withPublicDraw (M : G.PublicMonitoring) {R : Type} (ν : PMF R) :
    G.PublicMonitoring where
  Signal := R × M.Signal
  signalKernel := fun a => Math.ProbabilityMassFunction.prod ν (M.signalKernel a)

@[simp] theorem withPublicDraw_signalKernel
    (M : G.PublicMonitoring) {R : Type} (ν : PMF R) (a : Profile G) :
    (M.withPublicDraw ν).signalKernel a =
      Math.ProbabilityMassFunction.prod ν (M.signalKernel a) :=
  rfl

/-- Adding public draws leaves the original monitoring-signal marginal
unchanged. -/
@[simp] theorem withPublicDraw_signalKernel_map_snd
    (M : G.PublicMonitoring) {R : Type} (ν : PMF R) (a : Profile G) :
    ((M.withPublicDraw ν).signalKernel a).map Prod.snd = M.signalKernel a := by
  exact Math.ProbabilityMassFunction.prod_map_snd ν (M.signalKernel a)

/-- The new seed marginal is the fixed public draw law, independently of the
chosen action profile. -/
@[simp] theorem withPublicDraw_signalKernel_map_fst
    (M : G.PublicMonitoring) {R : Type} (ν : PMF R) (a : Profile G) :
    ((M.withPublicDraw ν).signalKernel a).map Prod.fst = ν := by
  exact Math.ProbabilityMassFunction.prod_map_fst ν (M.signalKernel a)

/-- A seeded monitored profile chooses an equilibrium profile after observing
the initial public seed. Subsequent seeds are components of the augmented
monitoring history. -/
abbrev SeededMonitoredProfile
    (M : G.PublicMonitoring) {R : Type} (ν : PMF R) :=
  R → (M.withPublicDraw ν).MonitoredProfile

/-- Normalized discounted payoff, averaged over the initial public seed. -/
def seededDiscountedAveragePayoff
    (M : G.PublicMonitoring) {R : Type} (ν : PMF R)
    (δ : ℝ) (σ : M.SeededMonitoredProfile ν) (who : ι) : ℝ :=
  Math.Probability.expect ν (fun r =>
    (M.withPublicDraw ν).discountedAveragePayoff δ (σ r) who)

/-- Sequential rationality for every publicly announced initial seed. Each
branch may condition future actions on the independently drawn future seeds. -/
def IsSeededPerfectPublicEquilibrium
    (M : G.PublicMonitoring) [DecidableEq ι]
    {R : Type} (ν : PMF R) (δ : ℝ)
    (σ : M.SeededMonitoredProfile ν) : Prop :=
  ∀ r, (M.withPublicDraw ν).IsPerfectPublicEquilibrium δ (σ r)

/-- Payoffs delivered by PPE profiles with a fixed pre-action public draw
device. -/
def seededPerfectPublicEquilibriumPayoffs
    (M : G.PublicMonitoring) [DecidableEq ι]
    {R : Type} (ν : PMF R) (δ : ℝ) : Set (Payoff ι) :=
  {v | ∃ σ : M.SeededMonitoredProfile ν,
    M.IsSeededPerfectPublicEquilibrium ν δ σ ∧
      ∀ who, M.seededDiscountedAveragePayoff ν δ σ who = v who}

/-- A seeded PPE payoff is a finite public randomization of PPE payoffs in the
monitoring structure augmented by future public draws. -/
theorem seededPerfectPublicEquilibriumPayoffs_subset_publicRandomized
    (M : G.PublicMonitoring) [DecidableEq ι]
    {R : Type} [Finite R] (ν : PMF R) (δ : ℝ) :
    M.seededPerfectPublicEquilibriumPayoffs ν δ ⊆
      (M.withPublicDraw ν).publicRandomizedPerfectPublicEquilibriumPayoffs δ := by
  rintro v ⟨σ, hσ, hv⟩
  let x : R → Payoff ι := fun r who =>
    (M.withPublicDraw ν).discountedAveragePayoff δ (σ r) who
  have hx (r : R) :
      x r ∈ (M.withPublicDraw ν).perfectPublicEquilibriumPayoffs δ :=
    ⟨σ r, hσ r, fun _ => rfl⟩
  have hmix := finitePublicRandomization_mem_publicRandomizedPPE
    (M.withPublicDraw ν) ν x hx
  have heq :
      (fun who => Math.Probability.expect ν (fun r =>
        (M.withPublicDraw ν).discountedAveragePayoff δ (σ r) who)) = v := by
    funext who
    exact hv who
  rw [← heq]
  exact hmix

/-- A constant family of augmented PPE profiles is a seeded PPE. -/
theorem isSeededPerfectPublicEquilibrium_const
    (M : G.PublicMonitoring) [DecidableEq ι]
    {R : Type} (ν : PMF R) {δ : ℝ}
    {σ : (M.withPublicDraw ν).MonitoredProfile}
    (hσ : (M.withPublicDraw ν).IsPerfectPublicEquilibrium δ σ) :
    M.IsSeededPerfectPublicEquilibrium ν δ (fun _ => σ) :=
  fun _ => hσ

/-- Averaging a constant augmented profile over the initial seed leaves its
discounted payoff unchanged. -/
@[simp] theorem seededDiscountedAveragePayoff_const
    (M : G.PublicMonitoring) {R : Type} (ν : PMF R)
    (δ : ℝ) (σ : (M.withPublicDraw ν).MonitoredProfile) (who : ι) :
    M.seededDiscountedAveragePayoff ν δ (fun _ => σ) who =
      (M.withPublicDraw ν).discountedAveragePayoff δ σ who := by
  simp [seededDiscountedAveragePayoff]

/-- Every augmented PPE payoff embeds into the seeded payoff set through a
constant initial-seed family. -/
theorem perfectPublicEquilibriumPayoffs_withPublicDraw_subset_seeded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {R : Type} (ν : PMF R) (δ : ℝ) :
    (M.withPublicDraw ν).perfectPublicEquilibriumPayoffs δ ⊆
      M.seededPerfectPublicEquilibriumPayoffs ν δ := by
  rintro v ⟨σ, hσ, hv⟩
  exact ⟨fun _ => σ, M.isSeededPerfectPublicEquilibrium_const ν hσ,
    fun who => by simpa using hv who⟩

end PublicMonitoring

end KernelGame

end GameTheory
