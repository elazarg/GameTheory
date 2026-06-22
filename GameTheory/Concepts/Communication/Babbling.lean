/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.Babbling
import GameTheory.Core.InertExtension
import GameTheory.Concepts.ZeroSum.ConstantSum
import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# Babbling Equilibria for Kernel Games

EU and `KernelGame` corollaries of the protocol-level babbling framework.

The protocol construction and preference-parametric `GameForm` theorem live in
`GameTheory.Core.Babbling`. This file imports solution concepts to state the
usual kernel-game/EU Nash consequences.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type} [DecidableEq ι]

/-- A base Nash equilibrium embeds as an enriched Nash equilibrium whenever the
enrichment preserves all unilateral Nash comparisons around babbling profiles. -/
theorem babbling_nashFor {F H : GameForm ι}
    {prefF : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    {prefH : ι → PMF H.Outcome → PMF H.Outcome → Prop}
    {proj : ∀ i, H.Strategy i → F.Strategy i}
    {embed : ∀ i, F.Strategy i → H.Strategy i}
    (hpres : F.BabblingDeviationPreservingFor H prefF prefH proj embed)
    {σ : F.Profile} (hN : F.IsNashFor prefF σ) :
    H.IsNashFor prefH (fun i => embed i (σ i)) := by
  rw [H.isNashFor_iff]
  intro who s'
  exact hpres σ who s' ((F.isNashFor_iff prefF σ).1 hN who (proj who s'))

namespace CheapTalkExtension

variable {F : GameForm ι}

/-- Every base Nash equilibrium embeds as a babbling Nash equilibrium in the
observable cheap-talk extension. -/
theorem babbling_nashFor (C : F.CheapTalkExtension)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {σ : F.Profile} (hN : F.IsNashFor pref σ) :
    C.form.IsNashFor pref (C.embedProfile σ) := by
  change C.form.IsNashFor pref (fun i => C.embed i (σ i))
  exact GameForm.babbling_nashFor (C.babblingDeviationPreservingFor pref) hN

end CheapTalkExtension

namespace InertExtension

variable {F : GameForm ι} (E : F.InertExtension)

/-- Inert extensions satisfy the local babbling-preservation condition. They
are the special case where the enriched outcome distribution factors through
projection at every profile, not just around babbling profiles. -/
theorem babblingDeviationPreservingFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop) :
    F.BabblingDeviationPreservingFor E.form pref pref E.proj E.embed := by
  intro σ who s' h
  change pref who
    (E.form.outcomeKernel (E.embedProfile σ))
    (E.form.outcomeKernel (Function.update (E.embedProfile σ) who s'))
  rw [E.outcomeKernel_form, E.outcomeKernel_form]
  simpa [E.projectProfile_update, E.project_embedProfile σ] using h

/-- Base Nash equilibria embed as babbling equilibria in an inert extension,
using only the local babbling-preservation theorem. -/
theorem babbling_nashFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    {σ : F.Profile} (hN : F.IsNashFor pref σ) :
    E.form.IsNashFor pref (E.embedProfile σ) := by
  exact GameForm.babbling_nashFor (E.babblingDeviationPreservingFor pref) hN

end InertExtension

end GameForm

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- Preference-parametric babbling theorem for kernel games. -/
theorem babbling_nashFor {G H : KernelGame ι}
    {prefG : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    {prefH : ι → PMF H.Outcome → PMF H.Outcome → Prop}
    {proj : ∀ i, H.Strategy i → G.Strategy i}
    {embed : ∀ i, G.Strategy i → H.Strategy i}
    (hpres : G.toGameForm.BabblingDeviationPreservingFor
      H.toGameForm prefG prefH proj embed)
    {σ : G.Profile} (hN : G.IsNashFor prefG σ) :
    H.IsNashFor prefH (fun i => embed i (σ i)) :=
  GameForm.babbling_nashFor hpres hN

/-- EU-specialized babbling theorem.

The hypothesis only compares utilities at embedded babbling profiles and their
unilateral enriched deviations; it does not require global EU preservation. -/
theorem babbling_nash {G H : KernelGame ι}
    (proj : ∀ i, H.Strategy i → G.Strategy i)
    (embed : ∀ i, G.Strategy i → H.Strategy i)
    (section_proj : ∀ i s, proj i (embed i s) = s)
    (babbling_eu : ∀ (σ : G.Profile) (who : ι) (s' : H.Strategy who),
      H.eu (Function.update (fun i => embed i (σ i)) who s') who =
        G.eu (Function.update σ who (proj who s')) who)
    {σ : G.Profile} (hN : G.IsNash σ) :
    H.IsNash (fun i => embed i (σ i)) := by
  intro who s'
  have hstatus :
      H.eu (fun i => embed i (σ i)) who = G.eu σ who := by
    have h := babbling_eu σ who (embed who (σ who))
    simpa [section_proj who (σ who)] using h
  have hdev :
      H.eu (Function.update (fun i => embed i (σ i)) who s') who =
        G.eu (Function.update σ who (proj who s')) who :=
    babbling_eu σ who s'
  calc
    H.eu (fun i => embed i (σ i)) who = G.eu σ who := hstatus
    _ ≥ G.eu (Function.update σ who (proj who s')) who := hN who (proj who s')
    _ = H.eu (Function.update (fun i => embed i (σ i)) who s') who := hdev.symm

end KernelGame

namespace KernelGame

variable {ι : Type} (G : KernelGame ι)

/-- Observable cheap-talk extension of the game form underlying a kernel game. -/
abbrev CheapTalkExtension := G.toGameForm.CheapTalkExtension

namespace CheapTalkExtension

variable {G}

/-- Reattach the base utility function to an observable cheap-talk extension. -/
def game (C : G.CheapTalkExtension) : KernelGame ι :=
  C.form.withUtility G.utility

section DecidableEq

variable [DecidableEq ι]

/-- In an observable cheap-talk extension, a unilateral deviation from a
babbling profile has the same expected utility as the projected base deviation.
-/
theorem babbling_eu (C : G.CheapTalkExtension)
    (σ : G.Profile) (who : ι) (s' : C.game.Strategy who) :
    C.game.eu (Function.update (C.embedProfile σ) who s') who =
      G.eu (Function.update σ who (C.proj who s')) who := by
  change expect
      (C.form.outcomeKernel (Function.update (C.embedProfile σ) who s'))
      (fun ω => G.utility ω who) =
    expect
      (G.outcomeKernel (Function.update σ who (C.proj who s')))
      (fun ω => G.utility ω who)
  rw [C.outcomeKernel_update_embedProfile σ who s']
  rfl

/-- Every Nash equilibrium of the base kernel game embeds as a babbling Nash
equilibrium in the observable cheap-talk extension. -/
theorem babbling_nash (C : G.CheapTalkExtension)
    {σ : G.Profile} (hN : G.IsNash σ) :
    C.game.IsNash (C.embedProfile σ) := by
  change C.game.IsNash (fun i => C.embed i (σ i))
  exact KernelGame.babbling_nash (G := G) (H := C.game)
    C.proj C.embed C.proj_embed C.babbling_eu hN

/-- Any pure Nash equilibrium of the observable cheap-talk extension induces a
Nash equilibrium of the base game via its on-path action profile.

The proof uses only same-message deviations: a player can keep their cheap-talk
message fixed and change the action prescribed at the realized message profile,
so cheap talk cannot turn a non-Nash on-path base profile into a pure Nash
profile of the extension. -/
theorem actionProfile_isNash_of_nash (C : G.CheapTalkExtension)
    {σ' : C.game.Profile} (hN : C.game.IsNash σ') :
    G.IsNash (C.actionProfile σ') := by
  intro who s
  have h := hN who ((σ' who).1, fun _ => s)
  change G.eu (C.actionProfile σ') who ≥
    G.eu (C.actionProfile
      (Function.update σ' who ((σ' who).1, fun _ => s))) who at h
  rw [C.actionProfile_update_sameMessage_constPlan σ' who s] at h
  exact h

/-- Observable cheap-talk pure Nash outcome laws are base-game Nash outcome laws:
given a cheap-talk Nash profile, its on-path action profile is a base Nash
profile and the two outcome kernels are definitionally the same. -/
theorem outcomeKernel_eq_base_nash_outcomeKernel_of_nash (C : G.CheapTalkExtension)
    {σ' : C.game.Profile} (hN : C.game.IsNash σ') :
    ∃ σ : G.Profile, G.IsNash σ ∧ C.game.outcomeKernel σ' = G.outcomeKernel σ := by
  exact ⟨C.actionProfile σ', C.actionProfile_isNash_of_nash hN, rfl⟩

/-- Observable cheap talk preserves exactly the set of pure-Nash outcome laws.

This is stronger than a utility-value statement and does not require utilities
to be injective: every cheap-talk Nash outcome law is generated by the on-path
base Nash action profile, while every base Nash outcome law is generated by its
babbling embedding. -/
theorem exists_nash_outcomeKernel_iff (C : G.CheapTalkExtension)
    (d : PMF G.Outcome) :
    (∃ σ' : C.game.Profile, C.game.IsNash σ' ∧ C.game.outcomeKernel σ' = d) ↔
      ∃ σ : G.Profile, G.IsNash σ ∧ G.outcomeKernel σ = d := by
  constructor
  · rintro ⟨σ', hN, hd⟩
    rcases C.outcomeKernel_eq_base_nash_outcomeKernel_of_nash hN with
      ⟨σ, hσN, hkernel⟩
    exact ⟨σ, hσN, hkernel.symm.trans hd⟩
  · rintro ⟨σ, hN, hd⟩
    exact ⟨C.embedProfile σ, C.babbling_nash hN, by simpa [hd]⟩

end DecidableEq

/-- In a two-player constant-sum game, observable cheap talk cannot change the
player-0 Nash value. -/
theorem constantSum_eu_eq_base_nash {G : KernelGame (Fin 2)}
    (C : G.CheapTalkExtension)
    [Finite G.Outcome] {c : ℝ} (hcs : G.IsConstantSum c)
    {σ' : C.game.Profile} (hN' : C.game.IsNash σ')
    {σ : G.Profile} (hN : G.IsNash σ) :
    C.game.eu σ' 0 = G.eu σ 0 := by
  have hproj : G.IsNash (C.actionProfile σ') :=
    C.actionProfile_isNash_of_nash hN'
  change G.eu (C.actionProfile σ') 0 = G.eu σ 0
  exact hcs.nash_eu_eq hproj hN

/-- In a two-player zero-sum game, observable cheap talk cannot change the
player-0 Nash value. -/
theorem zeroSum_eu_eq_base_nash {G : KernelGame (Fin 2)}
    (C : G.CheapTalkExtension)
    [Finite G.Outcome] (hzs : G.IsZeroSum)
    {σ' : C.game.Profile} (hN' : C.game.IsNash σ')
    {σ : G.Profile} (hN : G.IsNash σ) :
    C.game.eu σ' 0 = G.eu σ 0 :=
  C.constantSum_eu_eq_base_nash (c := 0) hzs hN' hN

end CheapTalkExtension

end KernelGame

end GameTheory
