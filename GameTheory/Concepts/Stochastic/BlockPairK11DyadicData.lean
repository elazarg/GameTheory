/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BlockPairK11LocalInterval

/-! # Exact dyadic box data for the block-pair K11 certificate -/

namespace GameTheory.BlockPairK11.DyadicCertificate

open LocalInterval Math.Interval

abbrev Precision : ℕ := 80

/-- Center of the exact reduced 31-variable box. -/
def center : HazardIndex → ℚ := ![
  0.070773162508252468, 0.060498957062486383,
  0.17873702678622647, 0.0087055416348124064,
  0.10205549180212524, 0.36082370743567099,
  0.16846473882967991, 0.065098107693290316,
  0.0097030523813587503, 0.28149267717706911,
  0.097545468121530698, 0.070330324639908015,
  0.002056179806325659, 0.060825485291417368,
  0.11501844773867245, 0.035699881913465702,
  0.0089701731507570524, 0.21708955986796688,
  0.060225550649685898, 0.16277294054551064,
  0.096127667694074562, 0.097209555464898692,
  0.17272500809879718, 0.050942654221662664,
  0.076391038430525665, 0.25317128934533362,
  0.024484008004623317, 0.0086400718059171568,
  0.053441876508934921, 0.013002213795957967,
  0.061305680651160738
]

/-- Sup-norm radius used by the reduced Krawczyk calculation. -/
def radius : ℚ := 1 / 100000000

/-- Outward-rounded precision-80 dyadic enclosure of the rational box. -/
def box (index : HazardIndex) : DyadicInterval Precision :=
  ⟨Rat.floor ((center index - radius) * DyadicInterval.scale Precision),
    Rat.ceil ((center index + radius) * DyadicInterval.scale Precision)⟩

end GameTheory.BlockPairK11.DyadicCertificate
