module

/-
EXP-178: arbitrary law-aware operators need not be kernel-linear.
One operator fails to preserve a binary mixture and cannot equal bind by one
fixed kernel for every input law. The result does not rule out selecting a
different kernel at each fixed law or require a new strategic-deviation API.
-/

public import GameTheory.Math.Probability.Mixture
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.ArenaLawTransform

open GameTheory.Math.Probability
open scoped ENNReal

/-- This operator inspects its whole input law rather than acting through one
fixed outcome kernel. -/
def transform (law : PMF Bool) : PMF Bool := by
  classical
  exact if law = PMF.pure false then PMF.pure true else PMF.pure false

def fair : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

theorem transform_pure_false : transform (PMF.pure false) = PMF.pure true := by
  simp [transform]

theorem transform_pure_true : transform (PMF.pure true) = PMF.pure false := by
  simp [transform]

theorem fair_ne_pure_false : fair ≠ PMF.pure false := by
  intro hequal
  have hatom := congrArg (fun law : PMF Bool => law true) hequal
  norm_num [fair, mix_apply] at hatom

theorem transform_fair : transform fair = PMF.pure false := by
  simp [transform, fair_ne_pure_false]

/-- Whole-law inspection breaks preservation of this one binary mixture. -/
theorem transform_not_preserve_mix :
    transform fair ≠ mix (1 / 2) (by norm_num) (by norm_num)
      (transform (PMF.pure false)) (transform (PMF.pure true)) := by
  intro hequal
  rw [transform_fair, transform_pure_false, transform_pure_true] at hequal
  have hatom := congrArg (fun law : PMF Bool => law true) hequal
  norm_num [mix_apply] at hatom

/-- There is no single outcome kernel realizing this operator for every input
law. This says nothing about choosing a different kernel for each fixed law. -/
theorem transform_not_uniform_kernel :
    ¬ ∃ kernel : Bool → PMF Bool, ∀ law, transform law = law.bind kernel := by
  rintro ⟨kernel, hkernel⟩
  apply transform_not_preserve_mix
  calc
    transform fair = fair.bind kernel := hkernel fair
    _ = mix (1 / 2) (by norm_num) (by norm_num)
        ((PMF.pure false).bind kernel) ((PMF.pure true).bind kernel) :=
      mix_bind (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true) kernel
    _ = mix (1 / 2) (by norm_num) (by norm_num)
        (transform (PMF.pure false)) (transform (PMF.pure true)) := by
      rw [← hkernel (PMF.pure false), ← hkernel (PMF.pure true)]

end GameTheory.Experimental.ArenaLawTransform
