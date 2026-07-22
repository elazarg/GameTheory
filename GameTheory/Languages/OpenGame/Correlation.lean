/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Compile
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Correlation.CorrelationRegimes

/-!
# Closed Correlation Devices for Open Games

Chance is not an atom of the deterministic open-game calculus: deterministic
`play` returns a value, not a distribution.  This file therefore gives closed
device shapes their own deliberately non-compositional semantics.

A private device samples a joint signal, privately shows coordinate `i` to
player `i`, and applies an obedience map.  Signal-dependent deviations recover
correlated equilibrium.  Restricting deviations to constant overrides recovers
coarse correlated equilibrium.  The revelation-direction theorems hold for
arbitrary signal spaces; canonical action recommendations give iff theorems.

A broadcast device publicly reveals one signal to every player.  Its
equilibrium condition is pointwise on the signal's support: every selected
pure profile must be Nash.  Thus it implements the pure-profile sunspot
regime and embeds into the library's more general `PublicSignalNash` regime.
-/

noncomputable section

namespace OpenGames

open GameTheory

/-- A closed private recommendation device for a kernel game. -/
structure PrivateDevice {ι : Type} (G : KernelGame ι)
    (Signal : ι → Type) where
  /-- Joint law of private signals. -/
  law : PMF (∀ i, Signal i)
  /-- Action played when a player obeys its private signal. -/
  obey : ∀ i, Signal i → G.Strategy i

namespace PrivateDevice

variable {ι : Type} [DecidableEq ι]
variable {G : KernelGame ι} {Signal : ι → Type}

/-- Obedient action profile induced by a signal profile. -/
def playProfile (d : PrivateDevice G Signal) (s : ∀ i, Signal i) : G.Profile :=
  fun i => d.obey i (s i)

/-- Distribution of action profiles induced by obedient play. -/
def inducedLaw (d : PrivateDevice G Signal) : PMF G.Profile :=
  d.law.map d.playProfile

/-- Profile produced by a signal-dependent deviation of one player. -/
def deviatedProfile (d : PrivateDevice G Signal) (who : ι)
    (dev : Signal who → G.Strategy who) (s : ∀ i, Signal i) : G.Profile :=
  Function.update (d.playProfile s) who (dev (s who))

/-- Distribution induced by a signal-dependent deviation. -/
def deviatedLaw (d : PrivateDevice G Signal) (who : ι)
    (dev : Signal who → G.Strategy who) : PMF G.Profile :=
  d.law.map (d.deviatedProfile who dev)

/-- Private-device equilibrium: no player gains from a deviation measurable
with respect to its own signal. -/
def IsEquilibrium (d : PrivateDevice G Signal) : Prop :=
  ∀ (who : ι) (dev : Signal who → G.Strategy who),
    G.correlatedEu (d.inducedLaw) who ≥
      G.correlatedEu (d.deviatedLaw who dev) who

/-- Ex-ante equilibrium: a player may ignore the device and choose a constant
action, but cannot condition that override on its recommendation. -/
def IsExAnteEquilibrium (d : PrivateDevice G Signal) : Prop :=
  ∀ (who : ι) (action : G.Strategy who),
    G.correlatedEu (d.inducedLaw) who ≥
      G.correlatedEu (d.deviatedLaw who (fun _signal => action)) who

/-- Canonical direct-recommendation device. -/
def canonical (G : KernelGame ι) (μ : PMF G.Profile) :
    PrivateDevice G G.Strategy where
  law := μ
  obey := fun _i action => action

omit [DecidableEq ι] in
@[simp]
theorem canonical_playProfile (μ : PMF G.Profile) (σ : G.Profile) :
    (canonical G μ).playProfile σ = σ := by
  rfl

omit [DecidableEq ι] in
@[simp]
theorem canonical_inducedLaw (μ : PMF G.Profile) :
    (canonical G μ).inducedLaw = μ := by
  unfold inducedLaw
  change μ.map id = μ
  exact PMF.map_id μ

/-- Deviating after the induced recommendation is the same law as deviating
directly as a correlated-equilibrium deviation. -/
theorem unilateralDeviationDistribution_inducedLaw
    (d : PrivateDevice G Signal) (who : ι)
    (dev : G.Strategy who → G.Strategy who) :
    G.unilateralDeviationDistribution d.inducedLaw who dev =
      d.deviatedLaw who (fun signal => dev (d.obey who signal)) := by
  unfold KernelGame.unilateralDeviationDistribution
  unfold KernelGame.deviationDistribution KernelGame.unilateralDeviation
  unfold inducedLaw deviatedLaw
  let f : G.Profile → G.Profile := fun σ =>
    Function.update σ who (dev (σ who))
  change (d.law.map d.playProfile).bind (PMF.pure ∘ f) =
    d.law.map (d.deviatedProfile who fun signal => dev (d.obey who signal))
  rw [PMF.bind_pure_comp, PMF.map_comp]
  rfl

/-- Canonical signal-dependent deviation is the library's unilateral
deviation distribution. -/
@[simp]
theorem canonical_deviatedLaw (μ : PMF G.Profile) (who : ι)
    (dev : G.Strategy who → G.Strategy who) :
    (canonical G μ).deviatedLaw who dev =
      G.unilateralDeviationDistribution μ who dev := by
  unfold KernelGame.unilateralDeviationDistribution
  unfold KernelGame.deviationDistribution KernelGame.unilateralDeviation
  unfold deviatedLaw
  let f : G.Profile → G.Profile := fun σ =>
    Function.update σ who (dev (σ who))
  change μ.map f = μ.bind (PMF.pure ∘ f)
  exact (PMF.bind_pure_comp f μ).symm

/-- Canonical constant override is the library's constant deviation
distribution. -/
@[simp]
theorem canonical_constantDeviatedLaw (μ : PMF G.Profile) (who : ι)
    (action : G.Strategy who) :
    (canonical G μ).deviatedLaw who (fun _signal => action) =
      G.constantDeviationDistribution μ who action := by
  unfold KernelGame.constantDeviationDistribution
  unfold KernelGame.deviationDistribution KernelGame.constantDeviation
  unfold deviatedLaw
  let f : G.Profile → G.Profile := fun σ => Function.update σ who action
  change μ.map f = μ.bind (PMF.pure ∘ f)
  exact (PMF.bind_pure_comp f μ).symm

/-- Constant deviation after the induced recommendation is exactly the device
law under a constant override. -/
theorem constantDeviationDistribution_inducedLaw
    (d : PrivateDevice G Signal) (who : ι) (action : G.Strategy who) :
    G.constantDeviationDistribution d.inducedLaw who action =
      d.deviatedLaw who (fun _signal => action) := by
  unfold KernelGame.constantDeviationDistribution
  unfold KernelGame.deviationDistribution KernelGame.constantDeviation
  unfold inducedLaw deviatedLaw
  let f : G.Profile → G.Profile := fun σ => Function.update σ who action
  change (d.law.map d.playProfile).bind (PMF.pure ∘ f) =
    d.law.map (d.deviatedProfile who fun _signal => action)
  rw [PMF.bind_pure_comp, PMF.map_comp]
  rfl

/-- Revelation direction for arbitrary private signals: equilibrium certifies
that the induced action law is a correlated equilibrium. -/
theorem IsEquilibrium.inducedLaw_isCorrelatedEq
    {d : PrivateDevice G Signal} (h : d.IsEquilibrium) :
    G.IsCorrelatedEq d.inducedLaw := by
  intro who dev
  rw [d.unilateralDeviationDistribution_inducedLaw who dev]
  exact h who fun signal => dev (d.obey who signal)

/-- Revelation direction for ex-ante devices: constant-override equilibrium
certifies a coarse correlated equilibrium. -/
theorem IsExAnteEquilibrium.inducedLaw_isCoarseCorrelatedEq
    {d : PrivateDevice G Signal} (h : d.IsExAnteEquilibrium) :
    G.IsCoarseCorrelatedEq d.inducedLaw := by
  intro who action
  rw [d.constantDeviationDistribution_inducedLaw who action]
  exact h who action

/-- Canonical private recommendations recover correlated equilibrium exactly. -/
theorem canonical_isEquilibrium_iff_isCorrelatedEq (μ : PMF G.Profile) :
    (canonical G μ).IsEquilibrium ↔ G.IsCorrelatedEq μ := by
  constructor
  · intro h
    simpa using h.inducedLaw_isCorrelatedEq
  · intro h who dev
    rw [canonical_inducedLaw, canonical_deviatedLaw]
    exact h who dev

/-- Canonical ex-ante recommendations recover coarse correlated equilibrium
exactly. -/
theorem canonical_isExAnteEquilibrium_iff_isCoarseCorrelatedEq
    (μ : PMF G.Profile) :
    (canonical G μ).IsExAnteEquilibrium ↔ G.IsCoarseCorrelatedEq μ := by
  constructor
  · intro h
    simpa using h.inducedLaw_isCoarseCorrelatedEq
  · intro h who action
    rw [canonical_inducedLaw, canonical_constantDeviatedLaw]
    exact h who action

end PrivateDevice

/-! ## Public broadcast / pure-profile sunspot devices -/

/-- A public signal selecting a pure action profile.  All players observe the
same signal before acting. -/
structure BroadcastDevice {ι : Type} (G : KernelGame ι) (Signal : Type) where
  /-- Law of the common signal. -/
  law : PMF Signal
  /-- Pure profile announced by each signal. -/
  play : Signal → G.Profile

namespace BroadcastDevice

variable {ι Signal : Type} [DecidableEq ι]
variable {G : KernelGame ι}

/-- Broadcast equilibrium: every on-support public announcement selects a
pure Nash profile.  Off-support announcements impose no condition. -/
def IsEquilibrium (d : BroadcastDevice G Signal) : Prop :=
  ∀ z, d.law z ≠ 0 → G.IsNash (d.play z)

/-- Pure-profile law induced by the broadcast device. -/
def inducedLaw (d : BroadcastDevice G Signal) : PMF G.Profile :=
  d.law.map d.play

/-- Canonical fully revealing broadcast of an action profile. -/
def canonical (G : KernelGame ι) (μ : PMF G.Profile) :
    BroadcastDevice G G.Profile where
  law := μ
  play := id

omit [DecidableEq ι] in
@[simp] theorem canonical_inducedLaw (μ : PMF G.Profile) :
    (canonical G μ).inducedLaw = μ := by
  exact PMF.map_id μ

/-- Canonical broadcast equilibrium is exactly Nash support. -/
theorem canonical_isEquilibrium_iff_nashSupport (μ : PMF G.Profile) :
    (canonical G μ).IsEquilibrium ↔
      ∀ σ, μ σ ≠ 0 → G.IsNash σ :=
  Iff.rfl

/-- A broadcast of pure profiles is the existing public-signal Nash regime
after embedding each pure profile as a point-mass mixed profile. -/
theorem isEquilibrium_iff_publicSignalNash [Fintype ι] [Finite G.Outcome]
    (d : BroadcastDevice G Signal) :
    d.IsEquilibrium ↔
      G.PublicSignalNash d.law (fun z => G.pureMixedProfile (d.play z)) := by
  constructor
  · intro h z hz
    exact (h z hz).pureMixedProfile_isNash
  · intro h z hz who action
    have hdev := h z hz who (PMF.pure action)
    rw [← G.pureMixedProfile_update (d.play z) who action,
      G.mixedExtension_eu_pureMixedProfile,
      G.mixedExtension_eu_pureMixedProfile] at hdev
    exact hdev

omit [DecidableEq ι] in
/-- The action law of a pure broadcast agrees with the general public-signal
construction. -/
theorem inducedLaw_eq_publicCorrelatedLaw [Fintype ι]
    (d : BroadcastDevice G Signal) :
    d.inducedLaw = G.publicCorrelatedLaw d.law
      (fun z => G.pureMixedProfile (d.play z)) := by
  unfold inducedLaw KernelGame.publicCorrelatedLaw
  simp_rw [Math.PMFProduct.pmfPi_pure]
  exact PMF.bind_pure_comp d.play d.law |>.symm

/-- Every equilibrium pure broadcast induces a correlated equilibrium. -/
theorem IsEquilibrium.inducedLaw_isCorrelatedEq [Finite ι] [Finite G.Outcome]
    {d : BroadcastDevice G Signal} (h : d.IsEquilibrium) :
    G.IsCorrelatedEq d.inducedLaw := by
  letI : Fintype ι := Fintype.ofFinite ι
  rw [d.inducedLaw_eq_publicCorrelatedLaw]
  exact ((d.isEquilibrium_iff_publicSignalNash).mp h).isCorrelatedEq

end BroadcastDevice

end OpenGames
