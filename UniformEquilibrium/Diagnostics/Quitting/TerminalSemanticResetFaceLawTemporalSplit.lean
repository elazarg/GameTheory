/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionTemporalSplit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionDiffuseClockBridge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTangentExtraction

/-!
# Temporal splitting of a retained law on a reset face

A joint terminal-semantic/law carrier point on the face `d_owner = 0` has
literal realizers which retain every positive law coordinate in a finite
window.  The reset coordinate of those same realizers tends to zero.  A
common square-root scale therefore makes the reset debt negligible, and the
retained window enters the existing concentrated-or-diffuse temporal split.

This result needs neither a surface-tension obstruction nor a fixed-law
minimization hypothesis.  It does not promote a selected suffix row to an
exact Nash row; it gives the exact profile-owned temporal alternatives which
such a promotion must consume.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- **A positive terminal-law coordinate on a reset face has an exhaustive
profile-owned temporal split.**

The literal profiles converge jointly to the prescribed semantic/law point.
Their selected finite windows retain more than half of the limiting coalition
mass.  On a strictly positive scale tending to zero, the displayed reset
player's initial debt is negligible.  Consequently the same profiles and
windows form either a concentrated marked-row packet or a diffuse coalition
clock packet.

The theorem deliberately stops at this temporal alternative: neither packet
asserts that a selected suffix row is an exact Nash--Bellman row. -/
theorem exists_resetFaceLaw_concentrated_or_diffuseWindowPacket
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (owner : iota)
    (terminal : {S : Finset iota // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hface : quittingTerminalSemanticDebt point.1 owner = 0)
    (hmass : 0 < point.2 (some terminal)) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      ∃ cutoff : ℕ → ℕ, ∃ scale : ℕ → ℝ,
        Tendsto (fun n ↦
          (quittingTerminalSemanticPair reward (profiles n),
            quittingTerminalOutcomeMass reward (profiles n)))
          atTop (nhds point) ∧
        (∀ n, 0 < scale n) ∧
        Tendsto scale atTop (nhds 0) ∧
        Tendsto (fun n ↦
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward (profiles n)) owner /
            scale n) atTop (nhds 0) ∧
        (∀ᶠ n in atTop,
          point.2 (some terminal) / 2 <
            quittingFiniteWindowCoalitionMass
              (profiles n) terminal (cutoff n)) ∧
        (Nonempty (QuittingReprojectionConcentratedPacket
            reward profiles owner terminal cutoff scale) ∨
          Nonempty (QuittingReprojectionDiffuseWindowPacket
            reward profiles owner terminal cutoff scale
              (point.2 (some terminal) / 2))) := by
  obtain ⟨profiles, cutoff, hprofiles, _hhalf, hwindowAtom⟩ :=
    exists_jointRealizers_finiteWindow_positiveStage_of_lawMass_pos
      reward point terminal hpoint hmass
  let debt : ℕ → ℝ := fun n ↦
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (profiles n)) owner
  have hsemantic : Tendsto (fun n ↦
      quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds point.1) :=
    continuous_fst.tendsto point |>.comp hprofiles
  have hdebtZero : Tendsto debt atTop (nhds 0) := by
    have hdebt :=
      (continuous_quittingTerminalSemanticDebt owner).tendsto point.1 |>.comp
        hsemantic
    rw [hface] at hdebt
    simpa only [debt, Function.comp_def] using hdebt
  have hdebtNonneg : ∀ n, 0 ≤ debt n := by
    intro n
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward
        (quittingTerminalSemanticPair_mem_carrier reward (profiles n)) owner
  obtain ⟨scale, hscalePos, _hscaleLe, hscaleZero, hdebtRate,
      _hnoLabels⟩ :=
    exists_commonVanishingResetScale (κ := Fin 0)
      debt (fun _ _ ↦ 0) hdebtNonneg (fun _ _ ↦ le_rfl)
        hdebtZero (fun label ↦ Fin.elim0 label)
  have hwindow : ∀ᶠ n in atTop,
      point.2 (some terminal) / 2 <
        quittingFiniteWindowCoalitionMass
          (profiles n) terminal (cutoff n) := by
    filter_upwards [hwindowAtom] with n hn
    simpa only [quittingFiniteWindowCoalitionMass] using hn.1
  have hlower : 0 < point.2 (some terminal) / 2 := by linarith
  have hsplit := exists_concentrated_or_diffuseWindowPacket
    (reward := reward) profiles owner terminal cutoff scale
      (point.2 (some terminal) / 2) hM hreward hlower hwindow hscalePos
        (by simpa only [debt] using hdebtRate)
  exact ⟨profiles, cutoff, scale, hprofiles, hscalePos, hscaleZero,
    by simpa only [debt] using hdebtRate, hwindow, hsplit⟩

/-- **A retained non-singleton law coordinate on a reset face cannot remain
temporally diffuse.**

If the original coalition clock is diffuse, delete the reset owner's hazard.
The deleted clock either exposes a recurrent opponent-absorption atom, which
the existing bridge turns into a concentrated packet with a fixed coalition
label, or remains diffuse.  The latter forces the original retained coalition
to be one opponent singleton, contradicting `hcollision`.

Thus every positive non-singleton law coordinate on a reset face supplies a
cofinally recurrent positive stage atom on the same convergent literal
profiles.  The atom's label may differ from the original retained coalition,
but it contains a fixed player distinct from the reset owner, and the reset
owner's survival-weighted row defect vanishes on the displayed scale. -/
theorem exists_resetFaceLaw_concentratedPacket_of_collision
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (owner : iota)
    (terminal : {S : Finset iota // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hface : quittingTerminalSemanticDebt point.1 owner = 0)
    (hmass : 0 < point.2 (some terminal))
    (hcollision : 1 < terminal.val.card) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      ∃ cutoff : ℕ → ℕ, ∃ scale : ℕ → ℝ,
      ∃ fixedOther : iota,
      ∃ exact : {S : Finset iota // S.Nonempty},
        Tendsto (fun n ↦
          (quittingTerminalSemanticPair reward (profiles n),
            quittingTerminalOutcomeMass reward (profiles n)))
          atTop (nhds point) ∧
        (∀ n, 0 < scale n) ∧
        Tendsto scale atTop (nhds 0) ∧
        fixedOther ≠ owner ∧ fixedOther ∈ exact.val ∧
        Nonempty (QuittingReprojectionConcentratedPacket
          reward profiles owner exact cutoff scale) := by
  obtain ⟨profiles, cutoff, scale, hprofiles, hscalePos, hscaleZero,
      _hdebtRate, _hwindow, hsplit⟩ :=
    exists_resetFaceLaw_concentrated_or_diffuseWindowPacket
      reward point owner terminal hM hreward hpoint hface hmass
  have hother : ∃ other ∈ terminal.val, other ≠ owner := by
    by_contra hnone
    push Not at hnone
    have hsubset : terminal.val ⊆ {owner} := by
      intro other hotherMem
      simp only [Finset.mem_singleton]
      exact hnone other hotherMem
    have hcardLe := Finset.card_le_card hsubset
    simp only [Finset.card_singleton] at hcardLe
    omega
  obtain ⟨other, hotherMem, hotherNe⟩ := hother
  rcases hsplit with hconcentrated | hdiffuse
  · exact ⟨profiles, cutoff, scale, other, terminal, hprofiles,
      hscalePos, hscaleZero, hotherNe, hotherMem, hconcentrated⟩
  · let packet := Classical.choice hdiffuse
    rcases packet.exists_concentrated_or_diffuseDeleted
        other hotherMem hotherNe hM hreward with hatom | hdeleted
    · obtain ⟨fixedOther, exact, hfixedNe, hfixedMem,
          hconcentrated⟩ := hatom
      exact ⟨profiles, cutoff, scale, fixedOther, exact, hprofiles,
        hscalePos, hscaleZero, hfixedNe, hfixedMem, hconcentrated⟩
    · have hsingleton : terminal.val = {other} :=
        (Classical.choice hdeleted).terminal_eq_singleton
          other hotherMem hotherNe
      rw [hsingleton] at hcollision
      simp at hcollision

end GameTheory
