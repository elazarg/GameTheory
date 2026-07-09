/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Math.PMFProduct
import Math.OnlineAlgorithms
import Math.Minimax.Loomis
import Math.LinearAlgebra.PerronFrobenius

/-!
# Math.Tests

Compilation validation entrypoint for project-local math infrastructure.
-/

namespace Math.Tests

open Math.Probability
open Math.PMFProduct

noncomputable section

example : expect (PMF.pure true) (fun b => if b then (3 : ℝ) else 0) = 3 := by
  simp

example :
    Kernel.comp (Kernel.id Bool) (Kernel.ofFun not) = Kernel.ofFun not := by
  simp

example (σ : Bool → Bool) :
    pmfPi (fun i => (PMF.pure (σ i) : PMF Bool)) = PMF.pure σ :=
  pmfPi_pure σ

end

namespace OnlineAlgorithms

open Math.OnlineAlgorithms

def stopOnTrue : OnlineAlgorithm Bool Unit Bool where
  init := ()
  step _ r := ((), r.bind fun b => if b then some true else none)

example : stopOnTrue.runResult () [false, true, false] = some true := by
  rfl

example : stopOnTrue.runAll () [false, true, true] = [true, true] := by
  rfl

end OnlineAlgorithms

namespace Minimax

example : Loomis.IsPositive (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) :=
  Loomis.IsPositive.one

example :
    ∃ (x : stdSimplex ℝ Unit) (y : stdSimplex ℝ Unit) (v : ℝ),
      (∀ j, v * Loomis.xB (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) x j
          ≤ Loomis.xA (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) x j) ∧
      (∀ i, Loomis.Ay (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) y i
          ≤ v * Loomis.By (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) y i) :=
  Loomis.loomis_theorem
    (fun (_ : Unit) (_ : Unit) => (1 : ℝ))
    (fun (_ : Unit) (_ : Unit) => (1 : ℝ))
    Loomis.IsPositive.one

example :
    ∃ (x y : stdSimplex ℝ (Fin 1)) (lam : ℝ),
      0 < lam ∧
      (∀ i, 0 < x.val i) ∧
      (∀ i, 0 < y.val i) ∧
      (∀ j, wsum x (fun _ => (1 : ℝ)) = lam * x.val j) ∧
      (∀ i, wsum y (fun _ => (1 : ℝ)) = lam * y.val i) :=
  Math.LinearAlgebra.perron_frobenius
    (n := 1) (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ))
    (by intro i j; norm_num)

end Minimax

end Math.Tests
