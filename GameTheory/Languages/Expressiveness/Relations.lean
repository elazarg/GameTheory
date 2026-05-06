import GameTheory.Languages.Expressiveness.Basic
import GameTheory.Core.GameSimulation
import GameTheory.Core.GameMorphism

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

/-! ## Expected-utility lens -/

/-- Directed expected-utility simulation.  This is weaker than utility-
distribution simulation: it preserves expected utilities, not payoff lotteries. -/
def ExpectedUtilitySimulation (G H : KernelGame ι) : Prop :=
  Nonempty (KernelGame.EUMorphism G H)

theorem expectedUtilitySimulation_refl (G : KernelGame ι) :
    ExpectedUtilitySimulation G G :=
  ⟨KernelGame.EUMorphism.id G⟩

theorem expectedUtilitySimulation_trans {G H K : KernelGame ι}
    (hGH : ExpectedUtilitySimulation G H)
    (hHK : ExpectedUtilitySimulation H K) :
    ExpectedUtilitySimulation G K := by
  rcases hGH with ⟨f⟩
  rcases hHK with ⟨g⟩
  exact ⟨KernelGame.EUMorphism.comp g f⟩

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
