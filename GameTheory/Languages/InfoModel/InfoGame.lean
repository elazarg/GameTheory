import GameTheory.Languages.InfoModel.SemanticForm

/-!
# GameTheory.Languages.InfoModel.InfoGame

Common-knowledge game layer over InfoModel.

`InfoModel` carries latent state and visibility.
`ControlModel` carries common-knowledge controller specifications.
`InfoGame` packages both as a game-level target for language compilation.
-/

namespace GameTheory

/-- Common-knowledge game layer built over an information model and control
structure. -/
structure InfoGame {ι σ : Type} {Act : ι → Type} where
  I : InfoModel ι σ Act
  C : ControlModel I

namespace InfoGame

variable {ι σ : Type} {Act : ι → Type}

/-- Build an `InfoGame` from an existing information model and common-
knowledge control layer. -/
def ofControlModel {I : InfoModel ι σ Act}
    (C : ControlModel I) : InfoGame (ι := ι) (σ := σ) (Act := Act) := ⟨I, C⟩

/-- Forget the common-knowledge control layer. -/
abbrev toInfoModel (G : InfoGame (ι := ι) (σ := σ) (Act := Act)) : InfoModel ι σ Act := G.I

/-- Access the controller specification at player `i`. -/
abbrev control (G : InfoGame (ι := ι) (σ := σ) (Act := Act)) (i : ι) :
    ControlSpec (G.I.Obs i) (Act i) :=
  G.C.control i

/-- Build an `InfoGame` with pure-utility control from per-player utility
    functions over observation histories. -/
def ofUtility {I : InfoModel ι σ Act}
    (u : ∀ i, List (I.Obs i) → ℝ) : InfoGame (ι := ι) (σ := σ) (Act := Act) :=
  ⟨I, ⟨fun i => .utility (u i)⟩⟩

/-- Build an `InfoGame` with behavioral control from per-player behavior laws
    over observation histories. -/
def ofBehavior {I : InfoModel ι σ Act}
    (β : ∀ i, List (I.Obs i) → PMF (Option (Act i))) :
    InfoGame (ι := ι) (σ := σ) (Act := Act) :=
  ⟨I, ⟨fun i => .behavior (β i)⟩⟩

end InfoGame

end GameTheory
