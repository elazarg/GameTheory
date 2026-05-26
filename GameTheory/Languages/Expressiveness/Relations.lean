/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Expressiveness.Basic
import GameTheory.Core.GameSimulation

/-!
# GameTheory.Languages.Expressiveness.Relations

Reusable semantic relations for language-expressiveness statements.

These definitions are thin wrappers around the existing core morphism and
isomorphism vocabulary.  They make the intended comparison lens explicit at the
language level.
-/

namespace GameTheory
namespace Languages
namespace Expressiveness

variable {ι : Type}

/-! ## Protocol lens -/

/-- Protocol equivalence: same outcome protocol up to strategy/outcome relabeling,
ignoring utilities. -/
def ProtocolEquivalent (G H : KernelGame ι) : Prop :=
  Nonempty (KernelGame.ProtocolIsomorphism G H)

theorem protocolEquivalent_refl (G : KernelGame ι) :
    ProtocolEquivalent G G :=
  ⟨GameForm.ProtocolIsomorphism.id G.toGameForm⟩

theorem protocolEquivalent_symm {G H : KernelGame ι}
    (h : ProtocolEquivalent G H) :
    ProtocolEquivalent H G := by
  rcases h with ⟨e⟩
  exact ⟨GameForm.ProtocolIsomorphism.symm e⟩

theorem protocolEquivalent_trans {G H K : KernelGame ι}
    (hGH : ProtocolEquivalent G H) (hHK : ProtocolEquivalent H K) :
    ProtocolEquivalent G K := by
  rcases hGH with ⟨eGH⟩
  rcases hHK with ⟨eHK⟩
  exact ⟨GameForm.ProtocolIsomorphism.comp eHK eGH⟩

/-- Equivalence lens for protocol-level expressiveness. -/
def protocolLens (ι : Type) : EquivalenceLens ι where
  Rel := ProtocolEquivalent
  refl := protocolEquivalent_refl
  symm := protocolEquivalent_symm
  trans := protocolEquivalent_trans

/-! ## Utility-distribution lens -/

/-- Directed utility-distribution simulation: a `KernelGame.Morphism` from `G`
to `H`. -/
def UtilityDistributionSimulation (G H : KernelGame ι) : Prop :=
  Nonempty (KernelGame.Simulation G H)

theorem utilityDistributionSimulation_refl (G : KernelGame ι) :
    UtilityDistributionSimulation G G :=
  ⟨KernelGame.Simulation.id G⟩

theorem utilityDistributionSimulation_trans {G H K : KernelGame ι}
    (hGH : UtilityDistributionSimulation G H)
    (hHK : UtilityDistributionSimulation H K) :
    UtilityDistributionSimulation G K := by
  rcases hGH with ⟨f⟩
  rcases hHK with ⟨g⟩
  exact ⟨KernelGame.Simulation.comp g f⟩

/-- Utility-distribution equivalence: invertible strategy relabeling preserving
the joint utility distribution at every profile. -/
def UtilityDistributionEquivalent (G H : KernelGame ι) : Prop :=
  Nonempty (KernelGame.Bisimulation G H)

theorem utilityDistributionEquivalent_refl (G : KernelGame ι) :
    UtilityDistributionEquivalent G G :=
  ⟨KernelGame.Bisimulation.id G⟩

theorem utilityDistributionEquivalent_symm {G H : KernelGame ι}
    (h : UtilityDistributionEquivalent G H) :
    UtilityDistributionEquivalent H G := by
  rcases h with ⟨e⟩
  exact ⟨KernelGame.Bisimulation.symm e⟩

theorem utilityDistributionEquivalent_trans {G H K : KernelGame ι}
    (hGH : UtilityDistributionEquivalent G H)
    (hHK : UtilityDistributionEquivalent H K) :
    UtilityDistributionEquivalent G K := by
  rcases hGH with ⟨eGH⟩
  rcases hHK with ⟨eHK⟩
  exact ⟨KernelGame.Bisimulation.comp eHK eGH⟩

/-- Default equivalence lens for semantic language expressiveness in this
library: preserve utility distributions, not only expected utilities. -/
def utilityDistributionLens (ι : Type) : EquivalenceLens ι where
  Rel := UtilityDistributionEquivalent
  refl := utilityDistributionEquivalent_refl
  symm := utilityDistributionEquivalent_symm
  trans := utilityDistributionEquivalent_trans

/-! ## Profile-map utility-distribution lens -/

/-- Directed utility-distribution simulation by a whole-profile map.

Unlike `UtilityDistributionSimulation`, this does not require the strategy
translation to factor player-by-player.  It is useful for bridges that already
prove utility-distribution preservation for a profile translation, but have not
yet exposed that translation as a `KernelGame.Morphism`. -/
def ProfileMapUtilityDistributionSimulation (G H : KernelGame ι) : Prop :=
  ∃ translateProfile : KernelGame.Profile G → KernelGame.Profile H,
    ∀ σ, H.udist (translateProfile σ) = G.udist σ

theorem profileMapUtilityDistributionSimulation_refl (G : KernelGame ι) :
    ProfileMapUtilityDistributionSimulation G G :=
  ⟨_root_.id, fun _ => rfl⟩

theorem profileMapUtilityDistributionSimulation_trans {G H K : KernelGame ι}
    (hGH : ProfileMapUtilityDistributionSimulation G H)
    (hHK : ProfileMapUtilityDistributionSimulation H K) :
    ProfileMapUtilityDistributionSimulation G K := by
  rcases hGH with ⟨f, hf⟩
  rcases hHK with ⟨g, hg⟩
  exact ⟨fun σ => g (f σ), fun σ => (hg (f σ)).trans (hf σ)⟩

/-- Directed preorder lens for utility-distribution preservation by arbitrary
profile translations. -/
def profileMapUtilityDistributionSimulationLens (ι : Type) : PreorderLens ι where
  Rel := ProfileMapUtilityDistributionSimulation
  refl := profileMapUtilityDistributionSimulation_refl
  trans := profileMapUtilityDistributionSimulation_trans

/-- Profile-map utility-distribution equivalence as mutual profile-map
simulation. -/
def ProfileMapUtilityDistributionEquivalent (G H : KernelGame ι) : Prop :=
  ProfileMapUtilityDistributionSimulation G H ∧
    ProfileMapUtilityDistributionSimulation H G

theorem profileMapUtilityDistributionEquivalent_refl (G : KernelGame ι) :
    ProfileMapUtilityDistributionEquivalent G G :=
  ⟨profileMapUtilityDistributionSimulation_refl G,
    profileMapUtilityDistributionSimulation_refl G⟩

theorem profileMapUtilityDistributionEquivalent_symm {G H : KernelGame ι}
    (h : ProfileMapUtilityDistributionEquivalent G H) :
    ProfileMapUtilityDistributionEquivalent H G :=
  ⟨h.2, h.1⟩

theorem profileMapUtilityDistributionEquivalent_trans {G H K : KernelGame ι}
    (hGH : ProfileMapUtilityDistributionEquivalent G H)
    (hHK : ProfileMapUtilityDistributionEquivalent H K) :
    ProfileMapUtilityDistributionEquivalent G K :=
  ⟨profileMapUtilityDistributionSimulation_trans hGH.1 hHK.1,
    profileMapUtilityDistributionSimulation_trans hHK.2 hGH.2⟩

/-- Equivalence lens for utility-distribution preservation by arbitrary
profile translations. -/
def profileMapUtilityDistributionLens (ι : Type) : EquivalenceLens ι where
  Rel := ProfileMapUtilityDistributionEquivalent
  refl := profileMapUtilityDistributionEquivalent_refl
  symm := profileMapUtilityDistributionEquivalent_symm
  trans := profileMapUtilityDistributionEquivalent_trans

/-! ## Expected-utility lens -/

/-- Per-player strategy translation preserving only expected utilities.

This is intentionally weaker than `KernelGame.EUMorphism`: the core
`EUMorphism` extends utility-distribution `Morphism`, while this expressiveness
lens is meant to ignore payoff lotteries and keep only expected values. -/
structure ExpectedUtilityMap (G H : KernelGame ι) where
  /-- Per-player strategy map. -/
  stratMap : ∀ i, G.Strategy i → H.Strategy i
  /-- Expected-utility preservation under mapped profiles. -/
  eu_preserved : ∀ (σ : KernelGame.Profile G) (who : ι),
    H.eu (fun i => stratMap i (σ i)) who = G.eu σ who

namespace ExpectedUtilityMap

/-- Identity expected-utility map. -/
def id (G : KernelGame ι) : ExpectedUtilityMap G G where
  stratMap := fun _i => _root_.id
  eu_preserved := by intro σ who; rfl

/-- Composition of expected-utility maps. -/
def comp {G H K : KernelGame ι}
    (g : ExpectedUtilityMap H K) (f : ExpectedUtilityMap G H) :
    ExpectedUtilityMap G K where
  stratMap := fun i => g.stratMap i ∘ f.stratMap i
  eu_preserved := by
    intro σ who
    let τ : KernelGame.Profile H := fun i => f.stratMap i (σ i)
    have hg : K.eu (fun i => g.stratMap i (τ i)) who = H.eu τ who :=
      g.eu_preserved τ who
    have hf : H.eu τ who = G.eu σ who := by
      simpa [τ] using f.eu_preserved σ who
    simpa [τ, Function.comp] using hg.trans hf

end ExpectedUtilityMap

/-- Directed expected-utility simulation.  This is weaker than utility-
distribution simulation: it preserves expected utilities, not payoff lotteries. -/
def ExpectedUtilitySimulation (G H : KernelGame ι) : Prop :=
  Nonempty (ExpectedUtilityMap G H)

theorem expectedUtilitySimulation_refl (G : KernelGame ι) :
    ExpectedUtilitySimulation G G :=
  ⟨ExpectedUtilityMap.id G⟩

theorem expectedUtilitySimulation_trans {G H K : KernelGame ι}
    (hGH : ExpectedUtilitySimulation G H)
    (hHK : ExpectedUtilitySimulation H K) :
    ExpectedUtilitySimulation G K := by
  rcases hGH with ⟨f⟩
  rcases hHK with ⟨g⟩
  exact ⟨ExpectedUtilityMap.comp g f⟩

/-- Expected-utility equivalence as mutual expected-utility simulation.  This is
the right coarse lens for strategic-form reductions that absorb chance into
payoff vectors. -/
def ExpectedUtilityEquivalent (G H : KernelGame ι) : Prop :=
  ExpectedUtilitySimulation G H ∧ ExpectedUtilitySimulation H G

theorem expectedUtilityEquivalent_refl (G : KernelGame ι) :
    ExpectedUtilityEquivalent G G :=
  ⟨expectedUtilitySimulation_refl G, expectedUtilitySimulation_refl G⟩

theorem expectedUtilityEquivalent_symm {G H : KernelGame ι}
    (h : ExpectedUtilityEquivalent G H) :
    ExpectedUtilityEquivalent H G :=
  ⟨h.2, h.1⟩

theorem expectedUtilityEquivalent_trans {G H K : KernelGame ι}
    (hGH : ExpectedUtilityEquivalent G H)
    (hHK : ExpectedUtilityEquivalent H K) :
    ExpectedUtilityEquivalent G K :=
  ⟨expectedUtilitySimulation_trans hGH.1 hHK.1,
    expectedUtilitySimulation_trans hHK.2 hGH.2⟩

/-- Coarser equivalence lens that preserves expected utilities only. -/
def expectedUtilityLens (ι : Type) : EquivalenceLens ι where
  Rel := ExpectedUtilityEquivalent
  refl := expectedUtilityEquivalent_refl
  symm := expectedUtilityEquivalent_symm
  trans := expectedUtilityEquivalent_trans

end Expressiveness
end Languages
end GameTheory
