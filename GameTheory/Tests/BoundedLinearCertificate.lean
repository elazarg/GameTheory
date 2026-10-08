import GameTheory.Math.BoundedLinearCertificate

/-! Negative coefficients and empty systems exercise generic bounded witnesses
independently of game semantics. -/

namespace GameTheory.Tests.BoundedLinearCertificate

open scoped BigOperators
open GameTheory.Math

-- The nonnegative solution is one half, despite the negative coefficient and RHS.
example : Nonempty (BoundedLinearCertificate
    (fun (_ : Fin 1) (_ : Fin 1) => (-2 : ℤ)) (fun _ => (-1 : ℤ))
    (linearCertificateWidth 1 1 1)) := by
  apply exists_bounded_nonnegative_linear_certificate
    (fun (_ : Fin 1) (_ : Fin 1) => (-2 : ℤ)) (fun _ => (-1 : ℤ)) 1
    (by decide) (by decide) (fun _ => (1 / 2 : ℝ))
  · intro j
    norm_num
  · intro i
    norm_num

-- Empty feasibility still needs a positive denominator and fits width one.
example : Nonempty (BoundedLinearCertificate
    (fun (i : Fin 0) (_ : Fin 0) => i.elim0) (fun i => i.elim0) 1) := by
  exact ⟨⟨1, Fin.elim0, by decide, by decide, fun i => i.elim0, fun i => i.elim0⟩⟩

end GameTheory.Tests.BoundedLinearCertificate
