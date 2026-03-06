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

/-- Common-knowledge game layer built over a latent machine and information
structure. This is the canonical game-level target for language compilation. -/
structure InfoGame {ι : Type} where
  M : LSM ι
  I : InfoModel M
  C : ControlModel M I

namespace InfoGame

variable {ι : Type}

/-- Build an `InfoGame` from an existing machine, information model, and common-
knowledge control layer. -/
def ofControlModel {M : LSM ι} {I : InfoModel M}
    (C : ControlModel M I) : InfoGame (ι := ι) := ⟨M, I, C⟩

/-- Forget the common-knowledge control layer. -/
abbrev toInfoModel (G : InfoGame (ι := ι)) : InfoModel G.M := G.I

/-- Access the controller specification at player `i`. -/
abbrev control (G : InfoGame (ι := ι)) (i : ι) :
    ControlSpec (G.I.Obs i) (G.M.Act i) :=
  G.C.control i

end InfoGame

end GameTheory
