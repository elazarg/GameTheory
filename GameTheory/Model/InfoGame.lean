import GameTheory.Model.SemanticForm

/-!
# GameTheory.Model.InfoGame

Common-knowledge game layer over the semantics-first core.

`InfoModel` carries latent state and visibility.
`ControlModel` carries common-knowledge controller specifications.
`InfoGame` packages both as the canonical game-level target for language
compilation, without replacing `KernelGame` as the strategic-form target.
-/

namespace GameTheory

/-- Common-knowledge game layer built over an information model and control
structure. This is the canonical game-level target for language compilation. -/
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

end InfoGame

end GameTheory
