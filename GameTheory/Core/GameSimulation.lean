import GameTheory.Core.GameMorphism

/-!
# GameTheory.Core.GameSimulation

Simulation/bisimulation vocabulary for games, layered over existing
distribution-preserving structures.

- `GameForm.Simulation` is `ProtocolMap`
- `GameForm.Bisimulation` is `ProtocolIsomorphism`
- `KernelGame.Simulation` is `KernelGame.Morphism`
- `KernelGame.Bisimulation` is `KernelGame.GameIsomorphism`
-/

namespace GameTheory

variable {ι : Type}

namespace GameForm

/-- Forward simulation at protocol level (distribution-preserving map). -/
abbrev Simulation (F F' : GameForm ι) : Type :=
  ProtocolMap F F'

/-- Bisimulation at protocol level (invertible protocol map). -/
abbrev Bisimulation (F F' : GameForm ι) : Type :=
  ProtocolIsomorphism F F'

end GameForm

namespace KernelGame

/-- Forward simulation at game level (distribution-preserving strategy map). -/
abbrev Simulation (G H : KernelGame ι) : Type :=
  Morphism G H

/-- Bisimulation at game level (invertible distribution-preserving map). -/
abbrev Bisimulation (G H : KernelGame ι) : Type :=
  GameIsomorphism G H

namespace Simulation

def id (G : KernelGame ι) : Simulation G G := Morphism.id G

def comp {G H K : KernelGame ι}
    (g : Simulation H K) (f : Simulation G H) : Simulation G K :=
  Morphism.comp g f

theorem udistPlayer_preserved {G H : KernelGame ι} (f : Simulation G H)
    (σ : Profile G) (who : ι) :
    H.udistPlayer (fun i => f.stratMap i (σ i)) who = G.udistPlayer σ who :=
  Morphism.udistPlayer_preserved f σ who

end Simulation

namespace Bisimulation

def id (G : KernelGame ι) : Bisimulation G G := GameIsomorphism.id G

def symm {G H : KernelGame ι} (e : Bisimulation G H) : Bisimulation H G :=
  GameIsomorphism.symm e

def comp {G H K : KernelGame ι}
    (g : Bisimulation H K) (f : Bisimulation G H) : Bisimulation G K :=
  GameIsomorphism.comp g f

def toSimulation {G H : KernelGame ι} (e : Bisimulation G H) : Simulation G H where
  stratMap := fun i => e.stratEquiv i
  udist_preserved := e.udist_preserved

theorem udistPlayer_preserved {G H : KernelGame ι} (e : Bisimulation G H)
    (σ : Profile G) (who : ι) :
    H.udistPlayer (fun i => e.stratEquiv i (σ i)) who = G.udistPlayer σ who :=
  GameIsomorphism.udistPlayer_preserved e σ who

end Bisimulation

end KernelGame

end GameTheory
