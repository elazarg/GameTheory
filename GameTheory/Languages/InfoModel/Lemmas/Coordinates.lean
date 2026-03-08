import GameTheory.Languages.InfoModel.SemanticForm

namespace GameTheory
namespace InfoModel

open Execution

variable {ι σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)

/-- Controller-local decision coordinate. -/
abbrev CoordIdx : Type := Σ i, I.LocalTrace i

/-- Flat pure policy indexed by coordinates. -/
abbrev FlatPolicy : Type := ∀ k : CoordIdx I, Option (Act k.1)

/-- Reassemble a coordinate-indexed flat policy into a standard pure profile. -/
def reassemblePolicy (ω : FlatPolicy I) : PureProfile I :=
  fun i v => ω ⟨i, v⟩

/-- Coordinate-wise agreement on a finite index set. -/
def agreeOn (J : Finset (CoordIdx I)) (ω₁ ω₂ : FlatPolicy I) : Prop :=
  ∀ k, k ∈ J → ω₁ k = ω₂ k

/-- Past-coordinate predicate at horizon `n`, measured on visible-history length. -/
def IsPastCoord (n : Nat) (k : CoordIdx I) : Prop :=
  k.2.2.length ≤ n

/-- Current queried coordinate predicate at run-state `ss`. -/
def IsNowCoord (ss : List σ) (k : CoordIdx I) : Prop :=
  ∃ i, k = ⟨i, I.projectStates i ss⟩

end InfoModel
end GameTheory
