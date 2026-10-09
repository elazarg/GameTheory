import GameTheory.Finite.BimatrixComplementaryCertificateBounds

/-! Binary width controls for normalized complementary certificates. -/
namespace GameTheory.Tests.BimatrixComplementaryCertificateBounds
open GameTheory.Finite

-- Positive and negative payoff shifts can produce opposite signed utilities.
example : ((complementaryNashCertificate (fun _ : Fin 1 => 2)
    (fun _ : Fin 2 => 1) 2 2).shiftPayoffs (-3) 4).FitsWidth (1 + (1 + 2) + 2 + 2) :=
  complementaryNashCertificate_fitsWidth _ _ 2 3 (-4) 1 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : ((complementaryNashCertificate (fun _ : Fin 1 => 2)
    (fun _ : Fin 2 => 1) 2 2).shiftPayoffs (-3) 4).rowUtilityNumerator = -4 := by
  decide +kernel

-- Empty dimensions still have field bounds, despite zero strategy masses.
example : ((complementaryNashCertificate (fun i : Fin 0 => i.elim0)
    (fun i : Fin 0 => i.elim0) 1 1).shiftPayoffs (-1) 1).FitsWidth (0 + (0 + 0) + 0 + 2) :=
  complementaryNashCertificate_fitsWidth _ _ 1 1 (-1) 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

-- Unit coordinates and denominator fit even when the input magnitude width is zero.
example : ((complementaryNashCertificate (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => 1) 1 1).shiftPayoffs (-1) (-1)).FitsWidth (0 + (1 + 1) + 0 + 2) :=
  complementaryNashCertificate_fitsWidth _ _ 1 1 1 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

end GameTheory.Tests.BimatrixComplementaryCertificateBounds
