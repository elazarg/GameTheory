import GameTheory.Math.GridBrouwerMap

/-! Controls for the displacement gap and the smallest affine self-map. -/

namespace GameTheory.Tests.GridBrouwer

open GameTheory.Math.Brouwer GameTheory.Math.Sperner

-- Two colors can have residual one third. The one-sixth acceptance threshold
-- excludes this false positive, even though its barycentric weights are valid.
example : weightedDisplacement 0 1 1 (1 / 3) (1 / 3) (1 / 3) = (-1 / 3, 1 / 3) := by
  norm_num [weightedDisplacement, colorDisplacement]

-- Boundary correction remains meaningful on a one-cell grid.
example : triangleBarycenterDisplacement (standardGridColor 1 (fun _ _ => 0))
    ⟨0, 0, false⟩ = (0, 0) := by
  norm_num [triangleBarycenterDisplacement, barycenterDisplacement,
    weightedDisplacement, standardGridColor, corner, colorDisplacement]

-- The barycenter is an actual fixed point of its local affine map.
example : triangleImage (standardGridColor 1 (fun _ _ => 0))
    ⟨0, 0, false⟩ (1 / 3) (1 / 3) (1 / 3) = (2 / 3, 1 / 3) := by
  norm_num [triangleImage, vertexImage, standardGridColor, corner, colorDisplacement]

end GameTheory.Tests.GridBrouwer
