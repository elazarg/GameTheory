import GameTheory.Model.SemanticForm

namespace GameTheory
namespace InfoModel

open Execution

variable {ι : Type} {M : LSM ι} (I : InfoModel M)

/-- Controller-local decision coordinate. -/
abbrev CoordIdx : Type := Σ i, (M.Label × I.LocalTrace i)

/-- Flat pure policy indexed by coordinates. -/
abbrev FlatPolicy : Type := ∀ k : CoordIdx I, Option (M.Act k.1)

/-- Reassemble a coordinate-indexed flat policy into a standard pure profile. -/
def reassemblePolicy (ω : FlatPolicy I) : PureProfile I :=
  fun i ℓ v => ω ⟨i, (ℓ, v)⟩

/-- Coordinate-wise agreement on a finite index set. -/
def agreeOn (J : Finset (CoordIdx I)) (ω₁ ω₂ : FlatPolicy I) : Prop :=
  ∀ k, k ∈ J → ω₁ k = ω₂ k

/-- Past-coordinate predicate at horizon `n` (by local-trace length). -/
def IsPastCoord (n : Nat) (k : CoordIdx I) : Prop :=
  k.2.2.length ≤ n

/-- Current queried coordinate predicate at run-state `hs`. -/
def IsNowCoord (hs : List M.Label × List M.State) (k : CoordIdx I) : Prop :=
  ∃ i ℓ, k = ⟨i, (ℓ, I.projectStates i hs.2)⟩

end InfoModel
end GameTheory
