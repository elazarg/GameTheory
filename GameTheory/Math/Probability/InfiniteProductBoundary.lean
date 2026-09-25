/-
# Atomic boundary for infinite-coordinate PMF laws

A PMF on a policy table has an atom. Increasingly diffuse coordinate laws
cannot be marginals of one such PMF, even though each finite prefix can be
sampled independently.
-/

import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.FiniteSampling
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ProductMeasure

namespace GameTheory.Math.Probability

open MeasureTheory ProbabilityTheory

noncomputable section

/-- No PMF on an infinite dependent table can have coordinate masses bounded
uniformly by a sequence tending to zero. -/
theorem no_pmf_of_marginal_bound_tendsto_zero {A : ℕ → Type*}
    (μ : PMF (∀ n, A n)) (bound : ℕ → ENNReal)
    (hzero : Filter.Tendsto bound Filter.atTop (nhds 0))
    (hmarginal : ∀ n (a : A n),
      (μ.map (fun policy => policy n)) a ≤ bound n) : False := by
  classical
  obtain ⟨policy, hpositive⟩ := μ.support_nonempty
  have hbound (n : ℕ) : μ policy ≤ bound n := by
    calc
      μ policy ≤ (μ.map (fun table => table n)) (policy n) := by
        rw [PMF.map_apply]
        convert (ENNReal.le_tsum
          (f := fun q => if policy n = q n then μ q else 0) policy) using 1
        · simp
      _ ≤ bound n := hmarginal n (policy n)
  have hlim : μ policy ≤ 0 := ge_of_tendsto' hzero hbound
  exact hpositive (le_antisymm hlim bot_le)

/-- A uniform `Fin (n + 1)` marginal at every coordinate is impossible for
a single PMF over all policies. -/
theorem no_uniform_finSucc_marginals
    (μ : PMF ((n : ℕ) → Fin (n + 1)))
    (hmarginal : ∀ n (a : Fin (n + 1)),
      (μ.map (fun policy => policy n)) a = ((n + 1 : ℕ) : ENNReal)⁻¹) : False := by
  refine no_pmf_of_marginal_bound_tendsto_zero μ
    (fun n => (n : ENNReal)⁻¹) ENNReal.tendsto_inv_nat_nhds_zero ?_
  intro n a
  rw [hmarginal]
  exact ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ n)

/-- Every finite family of those same uniform marginals is realized by one
PMF over total tables: sample the selected coordinates and fill the rest. -/
theorem finite_uniform_finSucc_marginals (sites : Finset ℕ) :
    ∃ μ : PMF ((n : ℕ) → Fin (n + 1)),
      ∀ n ∈ sites,
        μ.map (fun policy => policy n) =
          PMF.uniformOfFintype (Fin (n + 1)) := by
  classical
  let laws : (n : ℕ) → PMF (Fin (n + 1)) :=
    fun n => PMF.uniformOfFintype (Fin (n + 1))
  let fallback : (n : ℕ) → Fin (n + 1) := fun _ => 0
  refine ⟨FiniteAssignment.sampleOn laws sites fallback, ?_⟩
  intro n hn
  exact FiniteAssignment.sampleOn_map_eval_of_mem laws sites fallback hn

/-- Ordinary product measure realizes all the uniform dependent-coordinate
marginals that no PMF over total tables can realize. -/
def uniformFinSuccTableMeasure : Measure ((n : ℕ) → Fin (n + 1)) :=
  Measure.infinitePi fun n =>
    (PMF.uniformOfFintype (Fin (n + 1))).toMeasure

theorem uniformFinSuccTableMeasure_map_eval (n : ℕ) :
    uniformFinSuccTableMeasure.map
        (fun table : (k : ℕ) → Fin (k + 1) => table n) =
      (PMF.uniformOfFintype (Fin (n + 1))).toMeasure := by
  exact Measure.infinitePi_map_eval _ n

private def halfChance : unitInterval := ⟨1 / 2, by norm_num⟩

private theorem halfChance_ne_zero : halfChance ≠ 0 := by
  intro h
  have hh := congrArg Subtype.val h
  norm_num [halfChance] at hh

private theorem halfChance_ne_one : halfChance ≠ 1 := by
  intro h
  have hh := congrArg Subtype.val h
  norm_num [halfChance] at hh

/-- Every chance branch in the two-step hostile example has positive mass. -/
theorem halfChance_geometric_singleton_ne_zero (n : ℕ) :
    geometricMeasure (⟨1 / 2, by norm_num⟩ : unitInterval) {n} ≠ 0 := by
  have h : geometricMeasure halfChance {n} ≠ 0 := by
    rw [geometricMeasure_singleton halfChance_ne_zero]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (geometricMeasure_pos halfChance_ne_zero halfChance_ne_one n))
  exact h

/-- Draw a countably branching chance value, then read that coordinate from
one independently drawn total policy table. -/
def countableChanceTableOutcome : Measure (Σ n : ℕ, Fin (n + 1)) :=
  (geometricMeasure halfChance).bind fun n =>
    uniformFinSuccTableMeasure.map fun table =>
      (⟨n, table n⟩ : Σ k : ℕ, Fin (k + 1))

/-- The hostile two-step table law has exactly the sequential behavioral law:
after chance chooses `n`, the action is uniform on `Fin (n + 1)`. -/
theorem countableChanceTableOutcome_eq_sequential :
    countableChanceTableOutcome =
      (geometricMeasure (⟨1 / 2, by norm_num⟩ : unitInterval)).bind fun n =>
        ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure).map
          (fun a => (⟨n, a⟩ : Σ k : ℕ, Fin (k + 1))) := by
  unfold countableChanceTableOutcome
  apply Measure.bind_congr_right (Filter.Eventually.of_forall ?_)
  intro n
  calc
    _ = Measure.map (fun a => (⟨n, a⟩ : Σ k : ℕ, Fin (k + 1)))
          (uniformFinSuccTableMeasure.map
            (fun table : (k : ℕ) → Fin (k + 1) => table n)) := by
      simpa only [Function.comp_def] using
        (Measure.map_map (μ := uniformFinSuccTableMeasure)
          (g := fun a : Fin (n + 1) => (⟨n, a⟩ : Σ k : ℕ, Fin (k + 1)))
          (f := fun table : (k : ℕ) → Fin (k + 1) => table n)
          (by fun_prop) (by fun_prop)).symm
    _ = _ := by rw [uniformFinSuccTableMeasure_map_eval]

/-- Drawing the whole table before chance, as a pure-policy realization does,
has the same two-step law as drawing the independent chance value first. -/
theorem uniformFinSuccTableMeasure_bind_eval_comm
    (chance : Measure ℕ) [SFinite chance] :
    uniformFinSuccTableMeasure.bind (fun table =>
      chance.map (fun n => (⟨n, table n⟩ : Σ k : ℕ, Fin (k + 1)))) =
      chance.bind (fun n =>
        uniformFinSuccTableMeasure.map (fun table =>
          (⟨n, table n⟩ : Σ k : ℕ, Fin (k + 1)))) := by
  let : IsProbabilityMeasure uniformFinSuccTableMeasure := by
    unfold uniformFinSuccTableMeasure
    infer_instance
  let eval : (((n : ℕ) → Fin (n + 1)) × ℕ) →
      (Σ n : ℕ, Fin (n + 1)) :=
    fun p => ⟨p.2, p.1 p.2⟩
  have heval : Measurable eval := by
    apply measurable_from_prod_countable_left
    intro n
    have hcoord : Measurable
        (fun x : (k : ℕ) → Fin (k + 1) => x n) := by fun_prop
    have hmk : Measurable
        (fun a : Fin (n + 1) => (⟨n, a⟩ : Σ k : ℕ, Fin (k + 1))) := by fun_prop
    simpa only [eval, Function.comp_def] using hmk.comp hcoord
  have htable : ∀ table : (n : ℕ) → Fin (n + 1),
      Measurable (fun n => eval (table, n)) := by
    intro table
    exact measurable_of_countable _
  have hchance : ∀ n : ℕ,
      Measurable (fun table : (k : ℕ) → Fin (k + 1) =>
        eval (table, n)) := by
    intro n
    exact heval.comp (measurable_id.prodMk measurable_const)
  have hkernel : Measurable (fun table : (n : ℕ) → Fin (n + 1) =>
      chance.map (fun n => eval (table, n))) := by
    apply Measure.measurable_measure.2
    intro s hs
    have hmeasure := measurable_measure_prodMk_left (ν := chance) (heval hs)
    simpa only [Measure.map_apply (htable _) hs, Set.preimage,
      Set.mem_ofPred_eq] using hmeasure
  have hfirst :
      uniformFinSuccTableMeasure.bind (fun table =>
        chance.map (fun n => eval (table, n))) =
        (uniformFinSuccTableMeasure.prod chance).map eval := by
    ext s hs
    rw [Measure.bind_apply hs hkernel.aemeasurable,
      Measure.map_apply heval hs, Measure.prod_apply (heval hs)]
    simp only [Measure.map_apply (htable _) hs, Set.preimage,
      Set.mem_ofPred_eq]
  have hsecond :
      chance.bind (fun n => uniformFinSuccTableMeasure.map
        (fun table => eval (table, n))) =
        (uniformFinSuccTableMeasure.prod chance).map eval := by
    ext s hs
    rw [Measure.bind_apply hs (measurable_of_countable _).aemeasurable,
      Measure.map_apply heval hs,
      Measure.prod_apply_symm (heval hs)]
    simp only [Measure.map_apply (hchance _) hs, Set.preimage,
      Set.mem_ofPred_eq]
  exact hfirst.trans hsecond.symm

/-- The actual predraw-then-chance order realizes the sequential uniform
dependent action law at every positive-mass chance branch. -/
theorem countableChancePredrawnOutcome_eq_sequential :
    uniformFinSuccTableMeasure.bind (fun table =>
        (geometricMeasure (⟨1 / 2, by norm_num⟩ : unitInterval)).map (fun n =>
          (⟨n, table n⟩ : Σ k : ℕ, Fin (k + 1)))) =
      (geometricMeasure (⟨1 / 2, by norm_num⟩ : unitInterval)).bind (fun n =>
        ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure).map
          (fun a => (⟨n, a⟩ : Σ k : ℕ, Fin (k + 1)))) := by
  exact (uniformFinSuccTableMeasure_bind_eval_comm
    (geometricMeasure halfChance)).trans countableChanceTableOutcome_eq_sequential

end

end GameTheory.Math.Probability
