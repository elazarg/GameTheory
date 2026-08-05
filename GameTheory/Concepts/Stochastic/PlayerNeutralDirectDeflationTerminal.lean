/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralFullSupportDeflation

/-!
# Direct terminal route after player-neutral strict drift

The finite analytic-deflation theorem already iterates all later operational
deletions internally.  Consequently, an entry-reachable circulation on the
first zero-drift family can be extended by zero to that whole family and fed
directly to the terminal theorem.  No public child or global
three-coordinate recursion rank is needed for this analytic passage.

This applies before the support-rank dichotomy: neither selection of a
positive communicating class nor the full-support hypothesis is needed.
The full-support atlas branch is recorded as a corollary.

The resulting terminal alternative is still not a strategic certificate.
`PlayerNeutralDirectTerminalReconstructionAt` is the exact two-branch
eliminator needed to close it at a public entry and target.  Existing atlas
reconstructions for the analytic-circulation and zero-pairing terminal
leaves instantiate this single interface.  Thus the direct route removes
rank-child plumbing, but it does not derive the missing entry, whole-target,
and credibility/account arguments.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm
namespace PlayerNeutralStrictLeadingDrift

local instance directTerminalIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {entry : G.State}

/-- Extend an entry-reachable residual circulation by zero to the complete
zero-drift operational family.  Reachability and the selected class are not
used after this point. -/
theorem EntryReachablePositiveChargedCirculation.zeroDriftCirculation
    (reachable :
      EntryReachablePositiveChargedCirculation
        C.zeroDriftKernel C.zeroDriftSource C.zeroDriftCharge entry) :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn C.zeroDriftKernel C.zeroDriftSource)
      C.zeroDriftCharge := by
  classical
  let reachableState : FiniteDeflationState C.ZeroDriftIndex := {
    active :=
      reachableOccupationIndices
        C.zeroDriftKernel C.zeroDriftSource entry
  }
  let reachableFintype : Fintype reachableState.ActiveIndex :=
    reachableState.instFintypeActiveIndex
  letI : Fintype reachableState.ActiveIndex := reachableFintype
  have restricted :
      HasNormalizedPositiveChargedCirculation
        (fun index : reachableState.ActiveIndex =>
          actualOccupationColumn
            C.zeroDriftKernel C.zeroDriftSource index.1)
        (fun index : reachableState.ActiveIndex =>
          C.zeroDriftCharge index.1) := by
    refine ⟨reachable.mass, reachable.mass_nonneg, ?_, ?_⟩
    · intro destination
      rw [show
        (@Finset.univ reachableState.ActiveIndex reachableFintype) =
          (@Finset.univ reachableState.ActiveIndex
            (Finset.Subtype.fintype reachableState.active)) by
        ext index
        simp]
      exact reachable.balance destination
    · rw [show
        (@Finset.univ reachableState.ActiveIndex reachableFintype) =
          (@Finset.univ reachableState.ActiveIndex
            (Finset.Subtype.fintype reachableState.active)) by
        ext index
        simp]
      exact reachable.charge_eq_one
  exact restricted.extendActive reachableState
    (actualOccupationColumn C.zeroDriftKernel C.zeroDriftSource)
    C.zeroDriftCharge

/-- Reindex the zero-extended residual circulation on the fixed ambient
active subtype used by finite analytic deflation. -/
theorem EntryReachablePositiveChargedCirculation.zeroDriftDeflationState_hasEndpointCirculation
    (reachable :
      EntryReachablePositiveChargedCirculation
        C.zeroDriftKernel C.zeroDriftSource C.zeroDriftCharge entry) :
    HasNormalizedPositiveChargedCirculation
      (activeOccupationColumn C.zeroDriftDeflationState
        (germ.rawPlayerNeutralOccupationColumn who) 0)
      (activeOccupationCharge C.zeroDriftDeflationState
        (germ.rawPlayerNeutralOccupationCharge B who) 0) := by
  have residual :=
    EntryReachablePositiveChargedCirculation.zeroDriftCirculation
      (C := C) reachable
  let equiv :
      C.zeroDriftDeflationState.ActiveIndex ≃ C.ZeroDriftIndex :=
    C.zeroDriftIndexEquivActive.symm
  have active :=
    residual.reindex
      (actualOccupationColumn C.zeroDriftKernel C.zeroDriftSource)
      C.zeroDriftCharge equiv
  have equiv_value
      (index : C.zeroDriftDeflationState.ActiveIndex) :
      (equiv index).1 = index.1 := by
    rfl
  have column_eq :
      (fun index =>
        actualOccupationColumn
          C.zeroDriftKernel C.zeroDriftSource (equiv index)) =
        activeOccupationColumn C.zeroDriftDeflationState
          (germ.rawPlayerNeutralOccupationColumn who) 0 := by
    funext index destination
    change
      actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who)
          (equiv index).1 destination =
        germ.rawPlayerNeutralOccupationColumn
          who 0 index.1 destination
    rw [equiv_value]
    rw [germ.rawPlayerNeutralOccupationColumn_zero who]
  have charge_eq :
      (fun index => C.zeroDriftCharge (equiv index)) =
        activeOccupationCharge C.zeroDriftDeflationState
          (germ.rawPlayerNeutralOccupationCharge B who) 0 := by
    funext index
    change
      germ.playerNeutralOccupationCharge B who (equiv index).1 =
        germ.rawPlayerNeutralOccupationCharge B who 0 index.1
    rw [equiv_value]
    rw [germ.rawPlayerNeutralOccupationCharge_zero B who]
  rw [column_eq, charge_eq] at active
  exact active

/-- Run every remaining strict operational deletion internally and return
the final two-branch player-neutral terminal data. -/
theorem EntryReachablePositiveChargedCirculation.exists_playerNeutralDirectDeflationTerminalData
    (reachable :
      EntryReachablePositiveChargedCirculation
        C.zeroDriftKernel C.zeroDriftSource C.zeroDriftCharge entry)
    (terminalAnchor : G.State) :
    Nonempty
      (PlayerNeutralAnalyticDeflationTerminalData
        germ B who C.zeroDriftDeflationState terminalAnchor) :=
  germ.exists_playerNeutralAnalyticDeflationTerminalData
    B who C.zeroDriftDeflationState
    (EntryReachablePositiveChargedCirculation.zeroDriftDeflationState_hasEndpointCirculation
      (C := C) reachable)
    terminalAnchor

/-- If the original endpoint circulation is still in scope, strict drift
alone supplies the initial circulation for the same direct terminal
iterator; no reachable-class analysis is required. -/
theorem exists_playerNeutralDirectDeflationTerminalData_of_endpointCirculation
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (terminalAnchor : G.State) :
    Nonempty
      (PlayerNeutralAnalyticDeflationTerminalData
        germ B who C.zeroDriftDeflationState terminalAnchor) :=
  germ.exists_playerNeutralAnalyticDeflationTerminalData
    B who C.zeroDriftDeflationState
    (C.zeroDriftDeflationState_hasEndpointCirculation circulation)
    terminalAnchor

/-- The reachable-class package contains more than the direct terminal
route needs; its circulation alone starts the terminal iterator. -/
theorem ReachablePositiveClassData.exists_playerNeutralDirectDeflationTerminalData
    (data : C.ReachablePositiveClassData entry)
    (terminalAnchor : G.State) :
    Nonempty
      (PlayerNeutralAnalyticDeflationTerminalData
        germ B who C.zeroDriftDeflationState terminalAnchor) :=
  EntryReachablePositiveChargedCirculation.exists_playerNeutralDirectDeflationTerminalData
    (C := C) data.circulation terminalAnchor

end PlayerNeutralStrictLeadingDrift

/-- One reconstruction boundary for the two honest terminal branches.

These two maps are irreducible with the current semantic data: the first
must supply legal entry, whole-target transport, and credibility; the
second must resolve the active-harmonic obstruction. -/
structure PlayerNeutralDirectTerminalReconstructionAt
    (germ : G.AnalyticBellmanGerm)
    (entry : G.State) (error : ℝ)
    (B : G.State → Payoff ι) (who : ι)
    (initial :
      FiniteDeflationState
        (germ.PlayerNeutralOccupationIndex who))
    (terminalAnchor : G.State) : Type _ where
  analyticCirculation :
    PlayerNeutralAnalyticCirculationTerminalData
        germ B who initial terminalAnchor →
      G.IsAdaptivePotentialCertificateAt
        entry (germ.endpointValue entry) error
  zeroPairing :
    PlayerNeutralZeroPairingTerminalData
        germ B who initial terminalAnchor →
      G.IsAdaptivePotentialCertificateAt
        entry (germ.endpointValue entry) error

namespace PlayerNeutralDirectTerminalReconstructionAt

variable
    {germ : G.AnalyticBellmanGerm}
    {entry terminalAnchor : G.State} {error : ℝ}
    {B : G.State → Payoff ι} {who : ι}
    {initial :
      FiniteDeflationState
        (germ.PlayerNeutralOccupationIndex who)}

/-- Eliminate the operational terminal alternative through the single
direct reconstruction boundary. -/
theorem resolve
    (reconstruction :
      PlayerNeutralDirectTerminalReconstructionAt
        germ entry error B who initial terminalAnchor)
    (terminal :
      PlayerNeutralAnalyticDeflationTerminalData
        germ B who initial terminalAnchor) :
    G.IsAdaptivePotentialCertificateAt
      entry (germ.endpointValue entry) error := by
  cases terminal with
  | analyticCirculation data =>
      exact reconstruction.analyticCirculation data
  | zeroPairing data =>
      exact reconstruction.zeroPairing data

/-- The existing reconstruction interfaces of the two terminal atlas
leaves instantiate the unified direct-terminal boundary. -/
def ofAtlasTerminalReconstructions
    (analytic :
      EntryTargetReconstructionAt germ entry error
        (PlayerNeutralAnalyticTerminalEntryTargetData germ))
    (zero :
      ZeroPairingReconstructionAt germ entry error
        (PlayerNeutralZeroPairingObstructionData germ)) :
    PlayerNeutralDirectTerminalReconstructionAt
      germ entry error B who initial terminalAnchor where
  analyticCirculation := fun data =>
    analytic.closeEntryTarget {
      B := B
      who := who
      initial := initial
      terminalAnchor := terminalAnchor
      data := data
    }
  zeroPairing := fun data =>
    zero.resolveZeroPairing {
      B := B
      who := who
      initial := initial
      terminalAnchor := terminalAnchor
      data := data
    }

end PlayerNeutralDirectTerminalReconstructionAt

namespace PlayerNeutralStrictLeadingDrift

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}
    {C : germ.PlayerNeutralStrictLeadingDrift B who jet}
    {entry terminalAnchor : G.State}
    {error : ℝ}

/-- Strongest direct closure theorem: a reachable residual circulation
runs all remaining operational deflations and hands only the final
alternative to the unified reconstruction interface. -/
theorem EntryReachablePositiveChargedCirculation.directDeflationTerminalCertificate
    (reachable :
      EntryReachablePositiveChargedCirculation
        C.zeroDriftKernel C.zeroDriftSource C.zeroDriftCharge entry)
    (terminalAnchor : G.State)
    (reconstruction :
      PlayerNeutralDirectTerminalReconstructionAt
        germ entry error B who
          C.zeroDriftDeflationState terminalAnchor) :
    G.IsAdaptivePotentialCertificateAt
      entry (germ.endpointValue entry) error := by
  obtain ⟨terminal⟩ :=
    EntryReachablePositiveChargedCirculation.exists_playerNeutralDirectDeflationTerminalData
      (C := C) reachable terminalAnchor
  exact reconstruction.resolve terminal

end PlayerNeutralStrictLeadingDrift

namespace PlayerNeutralFullSupportData

variable
    {germ : G.AnalyticBellmanGerm}
    {entry terminalAnchor : G.State}
    {error : ℝ}

/-- A full-support strict-drift atlas leaf enters the generic terminal
iterator directly at its retained operational family.  The global
three-coordinate rank and public-child data are absent from the statement. -/
theorem exists_playerNeutralDirectDeflationTerminalData
    (data : PlayerNeutralFullSupportData germ entry)
    (terminalAnchor : G.State) :
    Nonempty
      (PlayerNeutralAnalyticDeflationTerminalData
        germ data.B data.who data.childOperationalState terminalAnchor) :=
  data.reachable.exists_playerNeutralDirectDeflationTerminalData
    terminalAnchor

/-- Direct terminal reconstruction closes the full-support branch without
constructing a rank-decreasing public child. -/
theorem directDeflationTerminalCertificate
    (data : PlayerNeutralFullSupportData germ entry)
    (terminalAnchor : G.State)
    (reconstruction :
      PlayerNeutralDirectTerminalReconstructionAt
        germ entry error data.B data.who
          data.childOperationalState terminalAnchor) :
    G.IsAdaptivePotentialCertificateAt
      entry (germ.endpointValue entry) error := by
  obtain ⟨terminal⟩ :=
    data.exists_playerNeutralDirectDeflationTerminalData terminalAnchor
  exact reconstruction.resolve terminal

/-- In particular, the pair of existing terminal-atlas reconstruction
interfaces closes the full-support branch through the direct route. -/
theorem directDeflationTerminalCertificate_of_atlas
    (data : PlayerNeutralFullSupportData germ entry)
    (terminalAnchor : G.State)
    (analytic :
      EntryTargetReconstructionAt germ entry error
        (PlayerNeutralAnalyticTerminalEntryTargetData germ))
    (zero :
      ZeroPairingReconstructionAt germ entry error
        (PlayerNeutralZeroPairingObstructionData germ)) :
    G.IsAdaptivePotentialCertificateAt
      entry (germ.endpointValue entry) error :=
  data.directDeflationTerminalCertificate terminalAnchor
    (.ofAtlasTerminalReconstructions analytic zero)

end PlayerNeutralFullSupportData
end AnalyticBellmanGerm

end StochasticGame
end GameTheory
