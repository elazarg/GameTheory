import GameTheory.Finite.BimatrixNashCertificateCorrectness

/-! Exact certificate controls with unequal denominators, failed best responses,
negative payoffs, and an empty action carrier. -/

namespace GameTheory.Tests.BimatrixNashCertificate

open GameTheory.Finite

private def thirdsFifths : NumeratorCertificate 2 :=
  ⟨![1, 2], ![2, 3], 3, 5, 15, 9⟩

example : verifyNashNumerators (fun _ _ => 3) thirdsFifths = true := by decide

example : verifyNashNumerators (fun _ _ => 4) thirdsFifths = false := by decide

example : verifyNashNumerators (fun _ _ => -3) thirdsFifths = false := by decide

example : verifyNashNumerators (q := 0) (fun _ _ => 0)
    ⟨fun i => i.elim0, fun i => i.elim0, 1, 1, 1, 1⟩ = false := by decide

noncomputable example :
    (GameTheory.MatrixGame.bimatrixGame (fun _ _ : Fin 2 => (3 : ℝ))
      (fun _ _ : Fin 2 => (3 : ℝ))).HasNashWithPayoffAtLeast (fun _ => 1) :=
  thirdsFifths.hasNash_of_valid (fun _ _ => 3) (by decide)

end GameTheory.Tests.BimatrixNashCertificate
