import Math.AnalyticPowerNormalization

noncomputable section

open Filter Set Topology

namespace Math
namespace GateGPositiveRootScratch

/-- The positive real `q`-th root, used to pull an approaching positive
parameter sequence back through a common Puiseux ramification. -/
def positiveNatRoot (q : ℕ) (x : ℝ) : ℝ :=
  x ^ ((q : ℝ)⁻¹)

theorem positiveNatRoot_pos
    {q : ℕ} {x : ℝ} (hx : 0 < x) :
    0 < positiveNatRoot q x :=
  Real.rpow_pos_of_pos hx _

theorem positiveNatRoot_pow
    {q : ℕ} (hq : 0 < q) {x : ℝ} (hx : 0 ≤ x) :
    positiveNatRoot q x ^ q = x := by
  rw [positiveNatRoot, ← Real.rpow_natCast,
    ← Real.rpow_mul hx]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  rw [inv_mul_cancel₀ hq0, Real.rpow_one]

theorem tendsto_positiveNatRoot
    {q : ℕ} (hq : 0 < q)
    {lam : ℕ → ℝ}
    (hlam_pos : ∀ n, 0 < lam n)
    (hlam : Tendsto lam atTop (𝓝 0)) :
    Tendsto (fun n => positiveNatRoot q (lam n))
      atTop (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  have hexponent : 0 < ((q : ℝ)⁻¹) := by positivity
  have hcontinuous :
      ContinuousAt (fun x : ℝ => positiveNatRoot q x) 0 := by
    simpa [positiveNatRoot, Real.zero_rpow hexponent.ne'] using
      Real.continuousAt_rpow_const
        0 ((q : ℝ)⁻¹) (Or.inr hexponent.le)
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa [Function.comp_def, positiveNatRoot,
      Real.zero_rpow hexponent.ne'] using
        hcontinuous.tendsto.comp hlam
  · exact Filter.Eventually.of_forall fun n =>
      positiveNatRoot_pos (hlam_pos n)

theorem positiveNatRoot_parameter
    {q : ℕ} (hq : 0 < q)
    {lam : ℕ → ℝ}
    (hlam_pos : ∀ n, 0 < lam n) :
    ∀ n, positiveNatRoot q (lam n) ^ q = lam n :=
  fun n => positiveNatRoot_pow hq (hlam_pos n).le

end GateGPositiveRootScratch
end Math
