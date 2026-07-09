/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Auctions.Combinatorial
import GameTheory.Auctions.VCG
import GameTheory.Implementation.Informational

/-!
# VCG k-implementation

Combinatorial-auction instantiation points for the frugal-VCG theorem in
Monderer--Tennenholtz. The conformance-bonus implementation theorem reuses the
frugal-VCG comparison lemma for `Q`-based deviations and the quasi-field
best-response comparison against arbitrary reports when opponents are
`Q`-based.
-/

namespace GameTheory

open scoped BigOperators
open Math.Probability

namespace CombinatorialAuction

variable {ι A : Type} [Fintype ι] [DecidableEq ι]
variable [DecidableEq A]

/-- A combinatorial allocation rule and Clarke-style `h` functions packaged as
an abstract `VCGSetup`. -/
noncomputable def vcgSetup
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i)) :
    VCGSetup ι where
  Θ := fun _ => Valuation A
  Outcome := Allocation ι A
  val := fun i v γ => v (γ.bundle i)
  alloc := d
  alloc_efficient := by
    intro θ γ
    simpa [surplus] using hd θ γ
  h := h
  h_indep := hh

/-- The direct informational game induced by a combinatorial VCG setup. -/
noncomputable abbrev informationalGame
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i)) : InformationalGame ι :=
  (vcgSetup d hd h hh).toInformationalGame

/-- Truthful reporting is an ex-post equilibrium in every combinatorial VCG
setup. -/
theorem truthfulStrategy_isExPostEq
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i)) :
    (informationalGame d hd h hh).IsExPostEq
      (vcgSetup d hd h hh).truthfulStrategy :=
  (vcgSetup d hd h hh).truthfulStrategy_isExPostEq

/-- Reports that are already bundled through `Q`. -/
def qBasedReport (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (_i : ι) (v : Valuation A) : Prop :=
  Valuation.IsBasedOn Q hQempty v

/-- The bundling strategy maps each true valuation to its `Q`-bundled report. -/
noncomputable def bundledTruthfulStrategy
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q) :
    (informationalGame d hd h hh).StrategyProfile :=
  fun _ v => Valuation.bundling Q hQempty v

/-! ## Bounded combinatorial VCG reports -/

/-- A valuation bounded above by `M` on every bundle. This is the bounded
valuation type used in the paper's VCG theorem. -/
abbrev BoundedValuation (A : Type) [DecidableEq A] (M : ℝ) :=
  {v : Valuation A // ∀ B, v B ≤ M}

namespace BoundedValuation

variable {M : ℝ}

instance instCoeFun (M : ℝ) : CoeFun (BoundedValuation A M) (fun _ => Finset A → ℝ) :=
  ⟨fun v => (v : Valuation A)⟩

theorem bound (v : BoundedValuation A M) (B : Finset A) :
    v B ≤ M :=
  v.2 B

theorem nonneg (v : BoundedValuation A M) (B : Finset A) :
    0 ≤ v B :=
  (v : Valuation A).nonneg B

/-- Bundling preserves a valuation upper bound. -/
noncomputable def bundling (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : BoundedValuation A M) : BoundedValuation A M :=
  ⟨Valuation.bundling Q hQempty (v : Valuation A), fun B =>
    (Valuation.bundling_le_original Q hQempty (v : Valuation A) B).trans
      (v.bound B)⟩

theorem bundling_isBasedOn (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (v : BoundedValuation A M) :
    Valuation.IsBasedOn Q hQempty (bundling Q hQempty v : Valuation A) :=
  Valuation.bundling_isBasedOn Q hQempty (v : Valuation A)

end BoundedValuation

/-- Forget boundedness from a bounded valuation profile. -/
def boundedValuationProfile {M : ℝ} (v : ι → BoundedValuation A M) :
    ι → Valuation A :=
  fun i => v i

omit [Fintype ι] in
@[simp] theorem boundedValuationProfile_update {M : ℝ}
    (v : ι → BoundedValuation A M) (i : ι) (vi : BoundedValuation A M) :
    boundedValuationProfile (Function.update v i vi) =
      Function.update (boundedValuationProfile v) i (vi : Valuation A) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [boundedValuationProfile]
  · simp [boundedValuationProfile, Function.update_of_ne hji]

/-- Surplus maximization for an allocation rule whose reports are bounded
valuations. -/
def IsBoundedSurplusMaximizer {M : ℝ}
    (d : (ι → BoundedValuation A M) → Allocation ι A) : Prop :=
  ∀ v γ, surplus (boundedValuationProfile v) (d v) ≥
    surplus (boundedValuationProfile v) γ

/-- Frugality for an allocation rule over bounded valuation reports. -/
def IsBoundedFrugal {M : ℝ}
    (d : (ι → BoundedValuation A M) → Allocation ι A) : Prop :=
  ∀ v i B, B ⊂ (d v).bundle i →
    (v i : Valuation A) B < (v i : Valuation A) ((d v).bundle i)

/-- The frugal surplus-maximizing allocation rule, restricted to bounded
valuation reports. -/
noncomputable def boundedFrugalSurplusMaximizingAllocation {M : ℝ} [Finite A]
    (v : ι → BoundedValuation A M) : Allocation ι A :=
  frugalSurplusMaximizingAllocation (ι := ι) (A := A)
    (boundedValuationProfile v)

theorem boundedFrugalSurplusMaximizingAllocation_isSurplusMaximizer
    {M : ℝ} [Finite A] :
    IsBoundedSurplusMaximizer
      (boundedFrugalSurplusMaximizingAllocation (ι := ι) (A := A) (M := M)) := by
  intro v γ
  exact frugalSurplusMaximizingAllocation_isSurplusMaximizer
    (ι := ι) (A := A) (boundedValuationProfile v) γ

theorem boundedFrugalSurplusMaximizingAllocation_isFrugal
    {M : ℝ} [Finite A] :
    IsBoundedFrugal
      (boundedFrugalSurplusMaximizingAllocation (ι := ι) (A := A) (M := M)) := by
  intro v i B hB
  exact frugalSurplusMaximizingAllocation_isFrugal
    (ι := ι) (A := A) (boundedValuationProfile v) i B hB

omit [Fintype ι] in
/-- In a bounded frugal allocation rule, a player reporting a `Q`-based bounded
valuation receives a bundle in `Q`. -/
lemma IsBoundedFrugal.allocated_bundle_mem_of_based {M : ℝ}
    {d : (ι → BoundedValuation A M) → Allocation ι A}
    (hfrugal : IsBoundedFrugal d)
    {Q : Finset (Finset A)} {hQempty : ∅ ∈ Q}
    {v : ι → BoundedValuation A M} {i : ι}
    (hbased : Valuation.IsBasedOn Q hQempty (v i : Valuation A)) :
    (d v).bundle i ∈ Q := by
  classical
  let B : Finset A := (d v).bundle i
  let feasible := Valuation.feasibleBundles Q B
  have hnonempty : feasible.Nonempty :=
    Valuation.feasibleBundles_nonempty hQempty B
  obtain ⟨C, hCfeasible, hsupC⟩ :=
    Finset.exists_mem_eq_sup' hnonempty (fun C : Finset A => (v i : Valuation A) C)
  rcases Finset.mem_filter.mp hCfeasible with ⟨hCQ, hCB⟩
  by_cases hCB_eq : C = B
  · rwa [hCB_eq] at hCQ
  · have hstrict : C ⊂ B := by
      refine ⟨hCB, ?_⟩
      intro hBC
      exact hCB_eq (Finset.Subset.antisymm hCB hBC)
    have hlt := hfrugal v i C hstrict
    have hB_eq_C : (v i : Valuation A) B = (v i : Valuation A) C := by
      calc
        (v i : Valuation A) B =
            Valuation.bundling Q hQempty (v i : Valuation A) B := (hbased B).symm
        _ = (v i : Valuation A) C := hsupC
    linarith

/-- A bounded combinatorial allocation rule and Clarke-style `h` functions
packaged as a VCG setup whose type/report space is bounded valuations. -/
noncomputable def boundedVcgSetup {M : ℝ}
    (d : (ι → BoundedValuation A M) → Allocation ι A)
    (hd : IsBoundedSurplusMaximizer d)
    (h : (i : ι) → (ι → BoundedValuation A M) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i)) :
    VCGSetup ι where
  Θ := fun _ => BoundedValuation A M
  Outcome := Allocation ι A
  val := fun i v γ => (v : Valuation A) (γ.bundle i)
  alloc := d
  alloc_efficient := by
    intro θ γ
    simpa [surplus, boundedValuationProfile] using hd θ γ
  h := h
  h_indep := hh

/-- The direct informational game induced by a bounded combinatorial VCG setup. -/
noncomputable abbrev boundedInformationalGame {M : ℝ}
    (d : (ι → BoundedValuation A M) → Allocation ι A)
    (hd : IsBoundedSurplusMaximizer d)
    (h : (i : ι) → (ι → BoundedValuation A M) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i)) : InformationalGame ι :=
  (boundedVcgSetup d hd h hh).toInformationalGame

/-- Bounded reports that are already bundled through `Q`. -/
def boundedQBasedReport {M : ℝ} (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q)
    (_i : ι) (v : BoundedValuation A M) : Prop :=
  Valuation.IsBasedOn Q hQempty (v : Valuation A)

/-- The bounded bundling strategy maps each true bounded valuation to its
`Q`-bundled bounded valuation. -/
noncomputable def boundedBundledTruthfulStrategy {M : ℝ}
    (d : (ι → BoundedValuation A M) → Allocation ι A)
    (hd : IsBoundedSurplusMaximizer d)
    (h : (i : ι) → (ι → BoundedValuation A M) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    (Q : Finset (Finset A)) (hQempty : ∅ ∈ Q) :
    (boundedInformationalGame d hd h hh).StrategyProfile :=
  fun _ v => BoundedValuation.bundling Q hQempty v

/-- True VCG utility in the combinatorial setup is the reported surplus with
player `i`'s report replaced by their true valuation, minus the `hᵢ` term. -/
theorem vcgSetup_trueUtility_eq_surplus_update
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    (i : ι) (vi : Valuation A) (report : ι → Valuation A) :
    (vcgSetup d hd h hh).trueUtility i vi report =
      surplus (Function.update report i vi) (d report) - h i report := by
  let V := vcgSetup d hd h hh
  rw [V.trueUtility_eq]
  have hsplit :
      surplus (Function.update report i vi) (d report) =
        vi ((d report).bundle i) +
          ∑ j ∈ Finset.univ.filter (· ≠ i),
            report j ((d report).bundle j) := by
    unfold surplus
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => (Function.update report i vi) j ((d report).bundle j))
      (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.sum_congr
      · ext j
        simp [Finset.mem_erase, Finset.mem_filter, and_comm]
      · intro j hj
        have hji : j ≠ i := by
          simpa [Finset.mem_filter] using hj
        simp [Function.update_of_ne hji]
  simpa [V, vcgSetup] using hsplit.symm

/-- True VCG utility in a bounded combinatorial setup, expressed using the
underlying unbounded valuation profile. -/
theorem boundedVcgSetup_trueUtility_eq_surplus_update {M : ℝ}
    (d : (ι → BoundedValuation A M) → Allocation ι A)
    (hd : IsBoundedSurplusMaximizer d)
    (h : (i : ι) → (ι → BoundedValuation A M) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    (i : ι) (vi : BoundedValuation A M)
    (report : ι → BoundedValuation A M) :
    (boundedVcgSetup d hd h hh).trueUtility i vi report =
      surplus (Function.update (boundedValuationProfile report) i (vi : Valuation A))
        (d report) - h i report := by
  let V := boundedVcgSetup d hd h hh
  rw [V.trueUtility_eq]
  have hsplit :
      surplus (Function.update (boundedValuationProfile report) i (vi : Valuation A))
          (d report) =
        (vi : Valuation A) ((d report).bundle i) +
          ∑ j ∈ Finset.univ.filter (· ≠ i),
            (report j : Valuation A) ((d report).bundle j) := by
    unfold surplus boundedValuationProfile
    rw [← Finset.add_sum_erase Finset.univ
      (fun j =>
        (Function.update (fun k => (report k : Valuation A)) i (vi : Valuation A)) j
          ((d report).bundle j))
      (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.sum_congr
      · ext j
        simp [Finset.mem_erase, Finset.mem_filter, and_comm]
      · intro j hj
        have hji : j ≠ i := by
          simpa [Finset.mem_filter] using hj
        simp [Function.update_of_ne hji]
  simpa [V, boundedVcgSetup] using hsplit.symm

/-- With unrestricted real-valued combinatorial valuations, any nonempty auction
has unbounded induced VCG utilities. Nontrivial concrete applications of the
bounded-payoff conformance-bonus theorems therefore need a bounded valuation
type or a custom bounded `VCGSetup`, as in the examples below. -/
theorem not_exists_uniform_bound_informationalGame
    [Finite A] [Nonempty A] [Nonempty ι]
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i)) :
    ¬ ∃ M : ℝ,
      ∀ θ a i, |(informationalGame d hd h hh).utility θ a i| ≤ M := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  rintro ⟨M, hbound⟩
  let i : ι := Classical.choice inferInstance
  let S : Finset A := Finset.univ
  have hS : S.Nonempty := by
    simp [S]
  let zeroVal : Valuation A :=
    { value := fun _ => 0
      empty_value := rfl
      monotone := by
        intro B C hBC
        rfl }
  let oneVal : Valuation A := Valuation.thresholdBundle S hS 1 (by norm_num)
  let report : ι → Valuation A := Function.update (fun _ : ι => zeroVal) i oneVal
  let fullAlloc : Allocation ι A :=
    { bundle := fun j => if j = i then S else ∅
      pairwise_disjoint := by
        intro j k hjk
        by_cases hji : j = i
        · by_cases hki : k = i
          · exact False.elim (hjk (hji.trans hki.symm))
          · simp [hji, hki]
        · simp [hji] }
  have hfull_surplus : surplus report fullAlloc = 1 := by
    unfold surplus
    rw [Finset.sum_eq_single i]
    · simp [report, fullAlloc, oneVal]
    · intro j _ hj
      simp [report, fullAlloc, zeroVal, Function.update_of_ne hj]
    · intro hi
      simp at hi
  have hsurplus_ge : 1 ≤ surplus report (d report) := by
    have hmax := hd report fullAlloc
    simpa [hfull_surplus] using hmax
  have hsurplus_eq_i : surplus report (d report) = oneVal ((d report).bundle i) := by
    unfold surplus
    rw [Finset.sum_eq_single i]
    · simp [report, oneVal]
    · intro j _ hj
      simp [report, zeroVal, Function.update_of_ne hj]
    · intro hi
      simp at hi
  have hsubset : S ⊆ (d report).bundle i := by
    by_contra hnot
    have hzero : oneVal ((d report).bundle i) = 0 :=
      Valuation.thresholdBundle_apply_of_not_subset hnot
    have hone : 1 ≤ oneVal ((d report).bundle i) := by
      simpa [hsurplus_eq_i] using hsurplus_ge
    linarith
  let H : ℝ := h i report
  let T : ℝ := max (M + H + 1) 0
  have hTnonneg : 0 ≤ T := le_max_right _ _
  let highVal : Valuation A := Valuation.thresholdBundle S hS T hTnonneg
  let θ : ι → Valuation A := Function.update (fun _ : ι => zeroVal) i highVal
  have hsurplus_high :
      surplus (Function.update report i (θ i)) (d report) = T := by
    unfold surplus
    rw [Finset.sum_eq_single i]
    · simp [report, θ, highVal, hsubset]
    · intro j _ hj
      simp [report, θ, zeroVal, Function.update_of_ne hj]
    · intro hi
      simp at hi
  have hutility :
      (informationalGame d hd h hh).utility θ report i = T - H := by
    change (vcgSetup d hd h hh).trueUtility i (θ i) report = T - H
    rw [vcgSetup_trueUtility_eq_surplus_update]
    simp [hsurplus_high, H]
  have hleM :
      (informationalGame d hd h hh).utility θ report i ≤ M :=
    (le_abs_self _).trans (hbound θ report i)
  have hgt : M < T - H := by
    have hmax : M + H + 1 ≤ T := le_max_left _ _
    linarith
  rw [hutility] at hleM
  linarith

/-- Lemma 1 from the paper, in combinatorial VCG form. For a frugal allocation
rule, reporting the bundled valuation `vᵢ^Q` weakly beats every `Q`-based own
report, against arbitrary reports of the other buyers. -/
theorem frugal_vcg_bundled_report_ge_qBased_report
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (hfrugal : IsFrugal d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    (i : ι) (vi : Valuation A) (report : ι → Valuation A)
    (wi : Valuation A) (hwi : Valuation.IsBasedOn Q hQempty wi) :
    (vcgSetup d hd h hh).trueUtility i vi
        (Function.update report i (Valuation.bundling Q hQempty vi)) ≥
      (vcgSetup d hd h hh).trueUtility i vi
        (Function.update report i wi) := by
  classical
  let viQ : Valuation A := Valuation.bundling Q hQempty vi
  let leftReport : ι → Valuation A := Function.update report i viQ
  let rightReport : ι → Valuation A := Function.update report i wi
  let trueReport : ι → Valuation A := Function.update report i vi
  let γ : Allocation ι A := d leftReport
  let δ : Allocation ι A := d rightReport
  have hγQ : γ.bundle i ∈ Q := by
    exact hfrugal.allocated_bundle_mem_of_based (d := d)
      (hQempty := hQempty) (v := leftReport) (i := i)
      (by
        simpa [leftReport, viQ] using
          Valuation.bundling_isBasedOn Q hQempty vi)
  have hδQ : δ.bundle i ∈ Q := by
    exact hfrugal.allocated_bundle_mem_of_based (d := d)
      (hQempty := hQempty) (v := rightReport) (i := i) (by
        simpa [rightReport] using hwi)
  have hleft_surplus :
      surplus leftReport γ = surplus trueReport γ := by
    unfold surplus
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · subst hji
      simp [leftReport, trueReport, viQ,
        Valuation.bundling_eq_original_of_mem (Q := Q) hQempty (v := vi) hγQ]
    · simp [leftReport, trueReport, Function.update_of_ne hji]
  have hright_surplus :
      surplus leftReport δ = surplus trueReport δ := by
    unfold surplus
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · subst hji
      simp [leftReport, trueReport, viQ,
        Valuation.bundling_eq_original_of_mem (Q := Q) hQempty (v := vi) hδQ]
    · simp [leftReport, trueReport, Function.update_of_ne hji]
  have hopt : surplus leftReport γ ≥ surplus leftReport δ := by
    simpa [leftReport, γ, δ] using hd leftReport δ
  have htrue_surplus : surplus trueReport γ ≥ surplus trueReport δ := by
    linarith
  have hh_eq : h i leftReport = h i rightReport := by
    have hind := hh i leftReport wi
    simpa [leftReport, rightReport, viQ, Function.update_idem] using hind
  have hleft_utility :
      (vcgSetup d hd h hh).trueUtility i vi leftReport =
        surplus trueReport γ - h i leftReport := by
    simpa [leftReport, trueReport, γ, viQ, Function.update_idem] using
      (vcgSetup_trueUtility_eq_surplus_update (d := d) (hd := hd)
        (h := h) (hh := hh) (i := i) (vi := vi) (report := leftReport))
  have hright_utility :
      (vcgSetup d hd h hh).trueUtility i vi rightReport =
        surplus trueReport δ - h i rightReport := by
    simpa [rightReport, trueReport, δ, Function.update_idem] using
      (vcgSetup_trueUtility_eq_surplus_update (d := d) (hd := hd)
        (h := h) (hh := hh) (i := i) (vi := vi) (report := rightReport))
  calc
    (vcgSetup d hd h hh).trueUtility i vi
        (Function.update report i (Valuation.bundling Q hQempty vi))
        = (vcgSetup d hd h hh).trueUtility i vi leftReport := rfl
    _ = surplus trueReport γ - h i leftReport := hleft_utility
    _ ≥ surplus trueReport δ - h i rightReport := by linarith
    _ = (vcgSetup d hd h hh).trueUtility i vi rightReport := hright_utility.symm
    _ = (vcgSetup d hd h hh).trueUtility i vi
        (Function.update report i wi) := rfl

/-- Holzman--Monderer best-response comparison in the combinatorial VCG
surface.  If every opponent reports a `Q`-based valuation, then reporting the
bundled true valuation weakly beats an arbitrary own report. -/
theorem frugal_vcg_bundled_report_ge_report_of_opponents_qBased
    [Fintype A]
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (hfrugal : IsFrugal d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q)
    (i : ι) (vi : Valuation A) (report : ι → Valuation A)
    (wi : Valuation A)
    (hopponents : ∀ j : ι, j ≠ i → Valuation.IsBasedOn Q hQ.empty_mem (report j)) :
    (vcgSetup d hd h hh).trueUtility i vi
        (Function.update report i (Valuation.bundling Q hQ.empty_mem vi)) ≥
      (vcgSetup d hd h hh).trueUtility i vi
        (Function.update report i wi) := by
  classical
  let viQ : Valuation A := Valuation.bundling Q hQ.empty_mem vi
  let leftReport : ι → Valuation A := Function.update report i viQ
  let rightReport : ι → Valuation A := Function.update report i wi
  let trueReport : ι → Valuation A := Function.update report i vi
  let γ : Allocation ι A := d leftReport
  let δ : Allocation ι A := d rightReport
  let ρ : Allocation ι A := δ.giveResidualTo i
  have hleft_based :
      ∀ j : ι, Valuation.IsBasedOn Q hQ.empty_mem (leftReport j) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [leftReport, viQ] using
        Valuation.bundling_isBasedOn Q hQ.empty_mem vi
    · simpa [leftReport, Function.update_of_ne hji] using hopponents j hji
  have hγQ : ∀ j : ι, γ.bundle j ∈ Q := by
    intro j
    exact hfrugal.allocated_bundle_mem_of_based (d := d)
      (hQempty := hQ.empty_mem) (v := leftReport) (i := j) (hleft_based j)
  have hright_opp_based :
      ∀ j : ι, j ≠ i → Valuation.IsBasedOn Q hQ.empty_mem (rightReport j) := by
    intro j hji
    simpa [rightReport, Function.update_of_ne hji] using hopponents j hji
  have hδOppQ : ∀ j : ι, j ≠ i → δ.bundle j ∈ Q := by
    intro j hji
    exact hfrugal.allocated_bundle_mem_of_based (d := d)
      (hQempty := hQ.empty_mem) (v := rightReport) (i := j)
      (hright_opp_based j hji)
  have hρiQ : δ.residualAfterOpponents i ∈ Q :=
    hQ.residualAfterOpponents_mem δ i hδOppQ
  have hleft_surplus_gamma :
      surplus leftReport γ = surplus trueReport γ := by
    unfold surplus
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · have hγiQ : γ.bundle i ∈ Q := by
        simpa [hji] using hγQ j
      simpa [leftReport, trueReport, viQ, hji] using
        Valuation.bundling_eq_original_of_mem (Q := Q) hQ.empty_mem
          (v := vi) hγiQ
    · simp [leftReport, trueReport, Function.update_of_ne hji]
  have hdelta_le_residual :
      surplus trueReport δ ≤ surplus leftReport ρ := by
    unfold surplus
    apply Finset.sum_le_sum
    intro j _
    by_cases hji : j = i
    · have hsubset : δ.bundle j ⊆ δ.residualAfterOpponents i := by
        simpa [hji] using δ.bundle_subset_residualAfterOpponents i
      have hval :
          vi (δ.bundle j) ≤ viQ (δ.residualAfterOpponents i) := by
        calc
          vi (δ.bundle j) ≤ vi (δ.residualAfterOpponents i) := vi.mono hsubset
          _ = viQ (δ.residualAfterOpponents i) := by
            symm
            simpa [viQ] using
              Valuation.bundling_eq_original_of_mem (Q := Q) hQ.empty_mem
                (v := vi) hρiQ
      simpa [trueReport, leftReport, ρ, viQ, hji] using hval
    · have hρj : ρ.bundle j = δ.bundle j := by
        simp [ρ, hji]
      simp [trueReport, leftReport, hρj, Function.update_of_ne hji]
  have htrue_surplus : surplus trueReport γ ≥ surplus trueReport δ := by
    change surplus trueReport δ ≤ surplus trueReport γ
    rw [← hleft_surplus_gamma]
    exact le_trans hdelta_le_residual (hd leftReport ρ)
  have hh_eq : h i leftReport = h i rightReport := by
    have hind := hh i leftReport wi
    simpa [leftReport, rightReport, viQ, Function.update_idem] using hind
  have hleft_utility :
      (vcgSetup d hd h hh).trueUtility i vi leftReport =
        surplus trueReport γ - h i leftReport := by
    simpa [leftReport, trueReport, γ, viQ, Function.update_idem] using
      (vcgSetup_trueUtility_eq_surplus_update (d := d) (hd := hd)
        (h := h) (hh := hh) (i := i) (vi := vi) (report := leftReport))
  have hright_utility :
      (vcgSetup d hd h hh).trueUtility i vi rightReport =
        surplus trueReport δ - h i rightReport := by
    simpa [rightReport, trueReport, δ, Function.update_idem] using
      (vcgSetup_trueUtility_eq_surplus_update (d := d) (hd := hd)
        (h := h) (hh := hh) (i := i) (vi := vi) (report := rightReport))
  calc
    (vcgSetup d hd h hh).trueUtility i vi
        (Function.update report i (Valuation.bundling Q hQ.empty_mem vi))
        = (vcgSetup d hd h hh).trueUtility i vi leftReport := rfl
    _ = surplus trueReport γ - h i leftReport := hleft_utility
    _ ≥ surplus trueReport δ - h i rightReport := by linarith
    _ = (vcgSetup d hd h hh).trueUtility i vi rightReport := hright_utility.symm
    _ = (vcgSetup d hd h hh).trueUtility i vi
        (Function.update report i wi) := rfl

/-- Bounded-valuation version of Lemma 1 from the paper. The statement is the
same weak VCG comparison as `frugal_vcg_bundled_report_ge_qBased_report`, but
the report/type space is the bounded valuation subtype used in Theorem 6. -/
theorem bounded_frugal_vcg_bundled_report_ge_qBased_report {M : ℝ}
    (d : (ι → BoundedValuation A M) → Allocation ι A)
    (hd : IsBoundedSurplusMaximizer d)
    (hfrugal : IsBoundedFrugal d)
    (h : (i : ι) → (ι → BoundedValuation A M) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQempty : ∅ ∈ Q)
    (i : ι) (vi : BoundedValuation A M)
    (report : ι → BoundedValuation A M)
    (wi : BoundedValuation A M)
    (hwi : boundedQBasedReport (ι := ι) Q hQempty i wi) :
    (boundedVcgSetup d hd h hh).trueUtility i vi
        (Function.update report i (BoundedValuation.bundling Q hQempty vi)) ≥
      (boundedVcgSetup d hd h hh).trueUtility i vi
        (Function.update report i wi) := by
  classical
  let viQ : BoundedValuation A M := BoundedValuation.bundling Q hQempty vi
  let leftReport : ι → BoundedValuation A M := Function.update report i viQ
  let rightReport : ι → BoundedValuation A M := Function.update report i wi
  let trueReport : ι → Valuation A :=
    Function.update (boundedValuationProfile report) i (vi : Valuation A)
  let γ : Allocation ι A := d leftReport
  let δ : Allocation ι A := d rightReport
  have hγQ : γ.bundle i ∈ Q := by
    exact hfrugal.allocated_bundle_mem_of_based (d := d)
      (hQempty := hQempty) (v := leftReport) (i := i)
      (by
        simpa [leftReport, viQ] using
          BoundedValuation.bundling_isBasedOn Q hQempty vi)
  have hδQ : δ.bundle i ∈ Q := by
    exact hfrugal.allocated_bundle_mem_of_based (d := d)
      (hQempty := hQempty) (v := rightReport) (i := i) (by
        simpa [boundedQBasedReport, rightReport] using hwi)
  have hleft_surplus :
      surplus (boundedValuationProfile leftReport) γ = surplus trueReport γ := by
    unfold surplus boundedValuationProfile
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · subst hji
      simpa [leftReport, trueReport, viQ, BoundedValuation.bundling] using
        Valuation.bundling_eq_original_of_mem (Q := Q) hQempty
          (v := (vi : Valuation A)) hγQ
    · simp [leftReport, trueReport, boundedValuationProfile, Function.update_of_ne hji]
  have hright_surplus :
      surplus (boundedValuationProfile leftReport) δ = surplus trueReport δ := by
    unfold surplus boundedValuationProfile
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · subst hji
      simpa [leftReport, trueReport, viQ, BoundedValuation.bundling] using
        Valuation.bundling_eq_original_of_mem (Q := Q) hQempty
          (v := (vi : Valuation A)) hδQ
    · simp [leftReport, trueReport, boundedValuationProfile, Function.update_of_ne hji]
  have hopt : surplus (boundedValuationProfile leftReport) γ ≥
      surplus (boundedValuationProfile leftReport) δ := by
    simpa [leftReport, γ, δ] using hd leftReport δ
  have htrue_surplus : surplus trueReport γ ≥ surplus trueReport δ := by
    linarith
  have hh_eq : h i leftReport = h i rightReport := by
    have hind := hh i leftReport wi
    simpa [leftReport, rightReport, viQ, Function.update_idem] using hind
  have hleft_utility :
      (boundedVcgSetup d hd h hh).trueUtility i vi leftReport =
        surplus trueReport γ - h i leftReport := by
    simpa [leftReport, trueReport, γ, viQ, Function.update_idem,
      boundedValuationProfile_update] using
      (boundedVcgSetup_trueUtility_eq_surplus_update (d := d) (hd := hd)
        (h := h) (hh := hh) (i := i) (vi := vi) (report := leftReport))
  have hright_utility :
      (boundedVcgSetup d hd h hh).trueUtility i vi rightReport =
        surplus trueReport δ - h i rightReport := by
    simpa [rightReport, trueReport, δ, Function.update_idem,
      boundedValuationProfile_update] using
      (boundedVcgSetup_trueUtility_eq_surplus_update (d := d) (hd := hd)
        (h := h) (hh := hh) (i := i) (vi := vi) (report := rightReport))
  calc
    (boundedVcgSetup d hd h hh).trueUtility i vi
        (Function.update report i (BoundedValuation.bundling Q hQempty vi))
        = (boundedVcgSetup d hd h hh).trueUtility i vi leftReport := rfl
    _ = surplus trueReport γ - h i leftReport := hleft_utility
    _ ≥ surplus trueReport δ - h i rightReport := by linarith
    _ = (boundedVcgSetup d hd h hh).trueUtility i vi rightReport :=
          hright_utility.symm
    _ = (boundedVcgSetup d hd h hh).trueUtility i vi
        (Function.update report i wi) := rfl

/-- Bounded-valuation Holzman--Monderer best-response comparison. If every
opponent reports a `Q`-based valuation, then reporting the bundled true
valuation weakly beats an arbitrary own bounded report. -/
theorem bounded_frugal_vcg_bundled_report_ge_report_of_opponents_qBased {M : ℝ}
    [Fintype A]
    (d : (ι → BoundedValuation A M) → Allocation ι A)
    (hd : IsBoundedSurplusMaximizer d)
    (hfrugal : IsBoundedFrugal d)
    (h : (i : ι) → (ι → BoundedValuation A M) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q)
    (i : ι) (vi : BoundedValuation A M)
    (report : ι → BoundedValuation A M)
    (wi : BoundedValuation A M)
    (hopponents :
      ∀ j : ι, j ≠ i → boundedQBasedReport Q hQ.empty_mem j (report j)) :
    (boundedVcgSetup d hd h hh).trueUtility i vi
        (Function.update report i (BoundedValuation.bundling Q hQ.empty_mem vi)) ≥
      (boundedVcgSetup d hd h hh).trueUtility i vi
        (Function.update report i wi) := by
  classical
  let viQ : BoundedValuation A M := BoundedValuation.bundling Q hQ.empty_mem vi
  let leftReport : ι → BoundedValuation A M := Function.update report i viQ
  let rightReport : ι → BoundedValuation A M := Function.update report i wi
  let trueReport : ι → Valuation A :=
    Function.update (boundedValuationProfile report) i (vi : Valuation A)
  let γ : Allocation ι A := d leftReport
  let δ : Allocation ι A := d rightReport
  let ρ : Allocation ι A := δ.giveResidualTo i
  have hleft_based :
      ∀ j : ι, Valuation.IsBasedOn Q hQ.empty_mem (leftReport j : Valuation A) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [leftReport, viQ] using
        BoundedValuation.bundling_isBasedOn Q hQ.empty_mem vi
    · simpa [leftReport, boundedQBasedReport, Function.update_of_ne hji] using
        hopponents j hji
  have hγQ : ∀ j : ι, γ.bundle j ∈ Q := by
    intro j
    exact hfrugal.allocated_bundle_mem_of_based (d := d)
      (hQempty := hQ.empty_mem) (v := leftReport) (i := j) (hleft_based j)
  have hright_opp_based :
      ∀ j : ι, j ≠ i →
        Valuation.IsBasedOn Q hQ.empty_mem (rightReport j : Valuation A) := by
    intro j hji
    simpa [rightReport, boundedQBasedReport, Function.update_of_ne hji] using
      hopponents j hji
  have hδOppQ : ∀ j : ι, j ≠ i → δ.bundle j ∈ Q := by
    intro j hji
    exact hfrugal.allocated_bundle_mem_of_based (d := d)
      (hQempty := hQ.empty_mem) (v := rightReport) (i := j)
      (hright_opp_based j hji)
  have hρiQ : δ.residualAfterOpponents i ∈ Q :=
    hQ.residualAfterOpponents_mem δ i hδOppQ
  have hleft_surplus_gamma :
      surplus (boundedValuationProfile leftReport) γ = surplus trueReport γ := by
    unfold surplus boundedValuationProfile
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · have hγiQ : γ.bundle i ∈ Q := by
        simpa [hji] using hγQ j
      simpa [leftReport, trueReport, viQ, BoundedValuation.bundling, hji] using
        Valuation.bundling_eq_original_of_mem (Q := Q) hQ.empty_mem
          (v := (vi : Valuation A)) hγiQ
    · simp [boundedValuationProfile, leftReport, trueReport, Function.update_of_ne hji]
  have hdelta_le_residual :
      surplus trueReport δ ≤ surplus (boundedValuationProfile leftReport) ρ := by
    unfold surplus boundedValuationProfile
    apply Finset.sum_le_sum
    intro j _
    by_cases hji : j = i
    · have hsubset : δ.bundle j ⊆ δ.residualAfterOpponents i := by
        simpa [hji] using δ.bundle_subset_residualAfterOpponents i
      have hval :
          (vi : Valuation A) (δ.bundle j) ≤
            (viQ : Valuation A) (δ.residualAfterOpponents i) := by
        calc
          (vi : Valuation A) (δ.bundle j) ≤
              (vi : Valuation A) (δ.residualAfterOpponents i) :=
            (vi : Valuation A).mono hsubset
          _ = (viQ : Valuation A) (δ.residualAfterOpponents i) := by
            symm
            simpa [viQ, BoundedValuation.bundling] using
              Valuation.bundling_eq_original_of_mem (Q := Q) hQ.empty_mem
                (v := (vi : Valuation A)) hρiQ
      simpa [trueReport, leftReport, ρ, viQ, hji] using hval
    · have hρj : ρ.bundle j = δ.bundle j := by
        simp [ρ, hji]
      simp [boundedValuationProfile, trueReport, leftReport, hρj,
        Function.update_of_ne hji]
  have htrue_surplus : surplus trueReport γ ≥ surplus trueReport δ := by
    change surplus trueReport δ ≤ surplus trueReport γ
    rw [← hleft_surplus_gamma]
    exact le_trans hdelta_le_residual (hd leftReport ρ)
  have hh_eq : h i leftReport = h i rightReport := by
    have hind := hh i leftReport wi
    simpa [leftReport, rightReport, viQ, Function.update_idem] using hind
  have hleft_utility :
      (boundedVcgSetup d hd h hh).trueUtility i vi leftReport =
        surplus trueReport γ - h i leftReport := by
    simpa [leftReport, trueReport, γ, viQ, Function.update_idem] using
      (boundedVcgSetup_trueUtility_eq_surplus_update (d := d) (hd := hd)
        (h := h) (hh := hh) (i := i) (vi := vi) (report := leftReport))
  have hright_utility :
      (boundedVcgSetup d hd h hh).trueUtility i vi rightReport =
        surplus trueReport δ - h i rightReport := by
    simpa [rightReport, trueReport, δ, Function.update_idem] using
      (boundedVcgSetup_trueUtility_eq_surplus_update (d := d) (hd := hd)
        (h := h) (hh := hh) (i := i) (vi := vi) (report := rightReport))
  calc
    (boundedVcgSetup d hd h hh).trueUtility i vi
        (Function.update report i (BoundedValuation.bundling Q hQ.empty_mem vi))
        = (boundedVcgSetup d hd h hh).trueUtility i vi leftReport := rfl
    _ = surplus trueReport γ - h i leftReport := hleft_utility
    _ ≥ surplus trueReport δ - h i rightReport := by linarith
    _ = (boundedVcgSetup d hd h hh).trueUtility i vi rightReport :=
          hright_utility.symm
    _ = (boundedVcgSetup d hd h hh).trueUtility i vi
        (Function.update report i wi) := rfl

/-- Bounded-valuation version of the paper's Theorem 6, factored at the
auction/game boundary. This is the faithful bounded report-space surface: the
generic conformance-bonus theorem supplies implementation, while bounded
frugal VCG supplies the Lemma 1 comparison against own `Q`-based deviations. -/
theorem boundedConformanceBonusTransfer_bundledTruthful_isSignalBlindExPostDominantKImplementation
    [Fintype A]
    {Mbar : ℝ}
    (d : (ι → BoundedValuation A Mbar) → Allocation ι A)
    (hd : IsBoundedSurplusMaximizer d)
    (hfrugal : IsBoundedFrugal d)
    (h : (i : ι) → (ι → BoundedValuation A Mbar) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q)
    {M B : ℝ} (hB : 0 ≤ B)
    (hbound :
      ∀ θ a i, |(boundedInformationalGame d hd h hh).utility θ a i| ≤ M)
    (hbonus : 2 * M ≤ B) :
    (boundedInformationalGame d hd h hh).IsSignalBlindExPostDominantKImplementation
      ((boundedInformationalGame d hd h hh).conformanceBonusTransfer
        (boundedQBasedReport (ι := ι) Q hQ.empty_mem) B)
      (boundedBundledTruthfulStrategy d hd h hh Q hQ.empty_mem) 0 := by
  exact InformationalGame.conformanceBonusTransfer_isSignalBlindExPostDominantKImplementation
    (G := boundedInformationalGame d hd h hh)
    (C := boundedQBasedReport (ι := ι) Q hQ.empty_mem)
    hB
    (by
      intro θ i
      exact BoundedValuation.bundling_isBasedOn Q hQ.empty_mem (θ i))
    hbound hbonus
    (by
      intro θ i a a' ha'
      simpa [boundedInformationalGame, boundedBundledTruthfulStrategy,
        boundedQBasedReport, VCGSetup.toInformationalGame] using
        bounded_frugal_vcg_bundled_report_ge_qBased_report
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQempty := hQ.empty_mem) (i := i) (vi := θ i)
          (report := a) (wi := a') ha')
    (by
      intro θ i a a' hopp
      simpa [boundedInformationalGame, boundedBundledTruthfulStrategy,
        boundedQBasedReport, VCGSetup.toInformationalGame] using
        bounded_frugal_vcg_bundled_report_ge_report_of_opponents_qBased
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQ := hQ) (i := i) (vi := θ i) (report := a) (wi := a')
          hopp)

/-- Equivalence-class form of the bounded VCG conformance-bonus theorem.  Under
the same weak hypotheses as the ex-post-dominant implementation theorem, the
surviving undominated signal-contingent strategies are exactly the strategies
utility-equivalent to the bundled truthful strategy. -/
theorem boundedConformanceBonusTransfer_bundledTruthful_undominatedStrategyProfiles_eq
    [Fintype A]
    {Mbar : ℝ}
    (d : (ι → BoundedValuation A Mbar) → Allocation ι A)
    (hd : IsBoundedSurplusMaximizer d)
    (hfrugal : IsBoundedFrugal d)
    (h : (i : ι) → (ι → BoundedValuation A Mbar) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q)
    {M B : ℝ}
    (hbound :
      ∀ θ a i, |(boundedInformationalGame d hd h hh).utility θ a i| ≤ M)
    (hbonus : 2 * M ≤ B) :
    (boundedInformationalGame d hd h hh).undominatedStrategyProfilesWithTransfer
        ((boundedInformationalGame d hd h hh).conformanceBonusTransfer
          (boundedQBasedReport (ι := ι) Q hQ.empty_mem) B) =
      {τ : (boundedInformationalGame d hd h hh).StrategyProfile |
        ∀ i, (boundedInformationalGame d hd h hh).StrategyEquivalentWithTransfer
          ((boundedInformationalGame d hd h hh).conformanceBonusTransfer
            (boundedQBasedReport (ι := ι) Q hQ.empty_mem) B)
          i (τ i) (boundedBundledTruthfulStrategy d hd h hh Q hQ.empty_mem i)} := by
  exact InformationalGame.conformanceBonusTransfer_undominatedStrategyProfiles_eq
    (G := boundedInformationalGame d hd h hh)
    (C := boundedQBasedReport (ι := ι) Q hQ.empty_mem)
    (σ := boundedBundledTruthfulStrategy d hd h hh Q hQ.empty_mem)
    (M := M) (B := B)
    (by
      intro θ i
      exact BoundedValuation.bundling_isBasedOn Q hQ.empty_mem (θ i))
    hbound hbonus
    (by
      intro θ i a a' ha'
      simpa [boundedInformationalGame, boundedBundledTruthfulStrategy,
        boundedQBasedReport, VCGSetup.toInformationalGame] using
        bounded_frugal_vcg_bundled_report_ge_qBased_report
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQempty := hQ.empty_mem) (i := i) (vi := θ i)
          (report := a) (wi := a') ha')
    (by
      intro θ i a a' hopp
      simpa [boundedInformationalGame, boundedBundledTruthfulStrategy,
        boundedQBasedReport, VCGSetup.toInformationalGame] using
        bounded_frugal_vcg_bundled_report_ge_report_of_opponents_qBased
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQ := hQ) (i := i) (vi := θ i) (report := a) (wi := a')
          hopp)

/-- Strict bounded-valuation version of the frugal-VCG conformance-bonus
theorem. As in the unbounded strict surface, frugality supplies only the weak
own-deviation comparison; strict implementation additionally requires explicit
strict witnesses for distinct `Q`-based deviations and an available
non-`Q`-based report for some opponent of each player. -/
theorem boundedConformanceBonusTransfer_bundledTruthful_isSignalBlindKImplementation_of_strict
    [Fintype A]
    {Mbar : ℝ}
    (d : (ι → BoundedValuation A Mbar) → Allocation ι A)
    (hd : IsBoundedSurplusMaximizer d)
    (hfrugal : IsBoundedFrugal d)
    (h : (i : ι) → (ι → BoundedValuation A Mbar) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q)
    {M B : ℝ} (hB : 0 ≤ B)
    (hsignal :
      ∀ i (si : (boundedInformationalGame d hd h hh).Signal i),
        ∃ θ : (boundedInformationalGame d hd h hh).SignalProfile, θ i = si)
    (hbound :
      ∀ θ a i, |(boundedInformationalGame d hd h hh).utility θ a i| ≤ M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : 2 * M < B)
    (hstrict_qBased_deviation :
      ∀ (i : ι) (vi wi : BoundedValuation A Mbar),
        boundedQBasedReport Q hQ.empty_mem i wi →
          wi ≠ BoundedValuation.bundling Q hQ.empty_mem vi →
            ∃ (θ : (boundedInformationalGame d hd h hh).SignalProfile)
              (a : (boundedInformationalGame d hd h hh).ActionProfile),
              θ i = vi ∧
                (boundedInformationalGame d hd h hh).utility θ
                    (Function.update a i
                      (boundedBundledTruthfulStrategy d hd h hh Q hQ.empty_mem i vi)) i >
                  (boundedInformationalGame d hd h hh).utility θ
                    (Function.update a i wi) i)
    (hopponent_non_qBased :
      ∀ i : ι, ∃ j : ι, j ≠ i ∧
        ∃ wj : BoundedValuation A Mbar,
          ¬ boundedQBasedReport Q hQ.empty_mem j wj) :
    (boundedInformationalGame d hd h hh).IsSignalBlindKImplementation
      ((boundedInformationalGame d hd h hh).conformanceBonusTransfer
        (boundedQBasedReport (ι := ι) Q hQ.empty_mem) B)
      ({boundedBundledTruthfulStrategy d hd h hh Q hQ.empty_mem} :
        Set (boundedInformationalGame d hd h hh).StrategyProfile) 0 := by
  classical
  exact InformationalGame.conformanceBonusTransfer_isSignalBlindKImplementation_of_strict
    (G := boundedInformationalGame d hd h hh)
    (C := boundedQBasedReport (ι := ι) Q hQ.empty_mem)
    hB
    (by
      intro θ i
      exact BoundedValuation.bundling_isBasedOn Q hQ.empty_mem (θ i))
    hsignal
    hbound hbonus_weak hbonus_strict
    (by
      intro θ i a a' ha'
      simpa [boundedInformationalGame, boundedBundledTruthfulStrategy,
        boundedQBasedReport, VCGSetup.toInformationalGame] using
        bounded_frugal_vcg_bundled_report_ge_qBased_report
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQempty := hQ.empty_mem) (i := i) (vi := θ i)
          (report := a) (wi := a') ha')
    (by
      intro θ i a a' hopp
      simpa [boundedInformationalGame, boundedBundledTruthfulStrategy,
        boundedQBasedReport, VCGSetup.toInformationalGame] using
        bounded_frugal_vcg_bundled_report_ge_report_of_opponents_qBased
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQ := hQ) (i := i) (vi := θ i) (report := a) (wi := a')
          hopp)
    (by
      intro i vi wi hwi hne
      simpa [boundedInformationalGame, boundedBundledTruthfulStrategy,
        boundedQBasedReport, VCGSetup.toInformationalGame] using
        hstrict_qBased_deviation i vi wi hwi hne)
    hopponent_non_qBased

/-- The paper's Theorem 6, factored at the auction/game boundary. Frugality
supplies the Lemma 1 comparison against every `Q`-based deviation, and the
quasi-field best-response theorem above supplies the comparison used when all
opponents already conform to the quasi-field.

For unrestricted real-valued valuation reports this is an assumption surface,
not a ready-to-instantiate auction theorem: `not_exists_uniform_bound_informationalGame`
shows that the uniform bounded-payoff hypothesis is unavailable in ordinary
nonempty unrestricted combinatorial auctions.  Use the bounded-valuation
versions above for concrete non-vacuous instances. -/
theorem conformanceBonusTransfer_bundledTruthful_isSignalBlindExPostDominantKImplementation
    [Fintype A]
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (hfrugal : IsFrugal d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q)
    {M B : ℝ} (hB : 0 ≤ B)
    (hbound :
      ∀ θ a i, |(informationalGame d hd h hh).utility θ a i| ≤ M)
    (hbonus : 2 * M ≤ B) :
    (informationalGame d hd h hh).IsSignalBlindExPostDominantKImplementation
      ((informationalGame d hd h hh).conformanceBonusTransfer
        (qBasedReport (ι := ι) Q hQ.empty_mem) B)
      (bundledTruthfulStrategy d hd h hh Q hQ.empty_mem) 0 := by
  exact InformationalGame.conformanceBonusTransfer_isSignalBlindExPostDominantKImplementation
    (G := informationalGame d hd h hh)
    (C := qBasedReport (ι := ι) Q hQ.empty_mem)
    hB
    (by
      intro θ i
      exact Valuation.bundling_isBasedOn Q hQ.empty_mem (θ i))
    hbound hbonus
    (by
      intro θ i a a' ha'
      simpa [informationalGame, bundledTruthfulStrategy, qBasedReport,
        VCGSetup.toInformationalGame] using
        frugal_vcg_bundled_report_ge_qBased_report
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQempty := hQ.empty_mem) (i := i) (vi := θ i)
          (report := a) (wi := a') ha')
    (by
      intro θ i a a' hopp
      simpa [informationalGame, bundledTruthfulStrategy, qBasedReport,
        VCGSetup.toInformationalGame] using
        frugal_vcg_bundled_report_ge_report_of_opponents_qBased
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQ := hQ) (i := i) (vi := θ i) (report := a) (wi := a') hopp)

/-- Equivalence-class form of the combinatorial VCG conformance-bonus theorem.
Under the same weak hypotheses as the ex-post-dominant implementation theorem,
the surviving undominated signal-contingent strategies are exactly the
strategies utility-equivalent to the bundled truthful strategy.

For unrestricted real-valued valuation reports this inherits the same bounded
utility caveat as
`conformanceBonusTransfer_bundledTruthful_isSignalBlindExPostDominantKImplementation`:
the local theorem is useful for custom bounded `VCGSetup`s, while the bounded
valuation surface above is the faithful concrete route. -/
theorem conformanceBonusTransfer_bundledTruthful_undominatedStrategyProfiles_eq
    [Fintype A]
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (hfrugal : IsFrugal d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q)
    {M B : ℝ}
    (hbound :
      ∀ θ a i, |(informationalGame d hd h hh).utility θ a i| ≤ M)
    (hbonus : 2 * M ≤ B) :
    (informationalGame d hd h hh).undominatedStrategyProfilesWithTransfer
        ((informationalGame d hd h hh).conformanceBonusTransfer
          (qBasedReport (ι := ι) Q hQ.empty_mem) B) =
      {τ : (informationalGame d hd h hh).StrategyProfile |
        ∀ i, (informationalGame d hd h hh).StrategyEquivalentWithTransfer
          ((informationalGame d hd h hh).conformanceBonusTransfer
            (qBasedReport (ι := ι) Q hQ.empty_mem) B)
          i (τ i) (bundledTruthfulStrategy d hd h hh Q hQ.empty_mem i)} := by
  exact InformationalGame.conformanceBonusTransfer_undominatedStrategyProfiles_eq
    (G := informationalGame d hd h hh)
    (C := qBasedReport (ι := ι) Q hQ.empty_mem)
    (σ := bundledTruthfulStrategy d hd h hh Q hQ.empty_mem)
    (M := M) (B := B)
    (by
      intro θ i
      exact Valuation.bundling_isBasedOn Q hQ.empty_mem (θ i))
    hbound hbonus
    (by
      intro θ i a a' ha'
      simpa [informationalGame, bundledTruthfulStrategy, qBasedReport,
        VCGSetup.toInformationalGame] using
        frugal_vcg_bundled_report_ge_qBased_report
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQempty := hQ.empty_mem) (i := i) (vi := θ i)
          (report := a) (wi := a') ha')
    (by
      intro θ i a a' hopp
      simpa [informationalGame, bundledTruthfulStrategy, qBasedReport,
        VCGSetup.toInformationalGame] using
        frugal_vcg_bundled_report_ge_report_of_opponents_qBased
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQ := hQ) (i := i) (vi := θ i) (report := a) (wi := a') hopp)

/-- Strict version of the frugal-VCG conformance-bonus theorem, factored so the
remaining strict content is explicit. Frugality supplies the weak Lemma 1
comparison against every `Q`-based own deviation; to get implementation by
undominated signal-contingent strategies, one additionally needs strict
witnesses for every distinct `Q`-based deviation and, for every buyer, some
other buyer with a non-`Q`-based report available.

This unbounded report-space surface is typically vacuous for ordinary
combinatorial auctions because the required uniform utility bound is ruled out
by `not_exists_uniform_bound_informationalGame`.  It is retained as a factored
interface for custom bounded setups; concrete bounded strict instances should
go through the bounded-valuation theorem above. -/
theorem conformanceBonusTransfer_bundledTruthful_isSignalBlindKImplementation_of_strict
    [Fintype A]
    (d : (ι → Valuation A) → Allocation ι A)
    (hd : IsSurplusMaximizer d)
    (hfrugal : IsFrugal d)
    (h : (i : ι) → (ι → Valuation A) → ℝ)
    (hh : ∀ i, IndependentOfCoordinate i (h i))
    {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q)
    {M B : ℝ} (hB : 0 ≤ B)
    (hbound :
      ∀ θ a i, |(informationalGame d hd h hh).utility θ a i| ≤ M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : 2 * M < B)
    (hstrict_qBased_deviation :
      ∀ (i : ι) (vi wi : Valuation A),
        qBasedReport Q hQ.empty_mem i wi →
          wi ≠ Valuation.bundling Q hQ.empty_mem vi →
            ∃ (θ : (informationalGame d hd h hh).SignalProfile)
              (a : (informationalGame d hd h hh).ActionProfile),
              θ i = vi ∧
                (informationalGame d hd h hh).utility θ
                    (Function.update a i
                      (bundledTruthfulStrategy d hd h hh Q hQ.empty_mem i vi)) i >
                  (informationalGame d hd h hh).utility θ
                    (Function.update a i wi) i)
    (hopponent_non_qBased :
      ∀ i : ι, ∃ j : ι, j ≠ i ∧
        ∃ wj : Valuation A, ¬ qBasedReport Q hQ.empty_mem j wj) :
    (informationalGame d hd h hh).IsSignalBlindKImplementation
      ((informationalGame d hd h hh).conformanceBonusTransfer
        (qBasedReport (ι := ι) Q hQ.empty_mem) B)
      ({bundledTruthfulStrategy d hd h hh Q hQ.empty_mem} :
        Set (informationalGame d hd h hh).StrategyProfile) 0 := by
  classical
  exact InformationalGame.conformanceBonusTransfer_isSignalBlindKImplementation_of_strict
    (G := informationalGame d hd h hh)
    (C := qBasedReport (ι := ι) Q hQ.empty_mem)
    hB
    (by
      intro θ i
      exact Valuation.bundling_isBasedOn Q hQ.empty_mem (θ i))
    (by
      intro i si
      change ∃ θ : ι → Valuation A, θ i = si
      exact ⟨Function.update (fun _ : ι => (default : Valuation A)) i si, by simp⟩)
    hbound hbonus_weak hbonus_strict
    (by
      intro θ i a a' ha'
      simpa [informationalGame, bundledTruthfulStrategy, qBasedReport,
        VCGSetup.toInformationalGame] using
        frugal_vcg_bundled_report_ge_qBased_report
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQempty := hQ.empty_mem) (i := i) (vi := θ i)
          (report := a) (wi := a') ha')
    (by
      intro θ i a a' hopp
      simpa [informationalGame, bundledTruthfulStrategy, qBasedReport,
        VCGSetup.toInformationalGame] using
        frugal_vcg_bundled_report_ge_report_of_opponents_qBased
          (d := d) (hd := hd) (hfrugal := hfrugal) (h := h) (hh := hh)
          (hQ := hQ) (i := i) (vi := θ i) (report := a) (wi := a') hopp)
    (by
      intro i vi wi hwi hne
      simpa [informationalGame, bundledTruthfulStrategy, qBasedReport,
        VCGSetup.toInformationalGame] using
        hstrict_qBased_deviation i vi wi hwi hne)
    hopponent_non_qBased

/-! ### Concrete bounded VCG witness -/

namespace BoundedOneGoodExample

/-- Two buyers in the smallest nontrivial bounded VCG example. -/
abbrev Buyer := Fin 2

/-- A buyer either has value `0` or value `1` for the single good. -/
abbrev Kind := Bool

/-- The outcome is either no sale or a winning buyer. -/
abbrev Outcome := Option Buyer

@[simp] theorem buyer_filter_ne_zero :
    Finset.univ.filter (fun j : Buyer => j ≠ 0) = {1} := by
  ext j
  fin_cases j <;> simp

@[simp] theorem buyer_filter_ne_one :
    Finset.univ.filter (fun j : Buyer => j ≠ 1) = {0} := by
  ext j
  fin_cases j <;> simp

/-- Value for the one-good allocation. `true` means value `1`; `false` means
value `0`. -/
def value (i : Buyer) (t : Kind) : Outcome → ℝ
  | none => 0
  | some j => if t then if j = i then 1 else 0 else 0

/-- Efficient allocation with deterministic tie-breaking toward buyer `0`. -/
def allocation (report : Buyer → Kind) : Outcome :=
  if report 0 then some 0 else if report 1 then some 1 else none

theorem allocation_efficient :
    ∀ report o, (∑ i : Buyer, value i (report i) (allocation report)) ≥
      ∑ i : Buyer, value i (report i) o := by
  intro report o
  cases h0 : report 0 <;> cases h1 : report 1 <;> cases o with
  | none => norm_num [Fin.sum_univ_two, allocation, value, h0, h1]
  | some j =>
      fin_cases j <;> norm_num [Fin.sum_univ_two, allocation, value, h0, h1]

def zeroH (_i : Buyer) (_report : Buyer → Kind) : ℝ :=
  0

theorem zeroH_independent :
    ∀ i, IndependentOfCoordinate i (zeroH i) := by
  intro i report t
  rfl

/-- A concrete bounded VCG setup with two buyers and one binary-valued good. -/
noncomputable def setup : VCGSetup Buyer where
  Θ := fun _ => Kind
  Outcome := Outcome
  val := value
  alloc := allocation
  alloc_efficient := allocation_efficient
  h := zeroH
  h_indep := zeroH_independent

theorem utility_abs_le_one
    (θ : setup.toInformationalGame.SignalProfile)
    (a : setup.toInformationalGame.ActionProfile) (i : Buyer) :
    |setup.toInformationalGame.utility θ a i| ≤ 1 := by
  change |setup.trueUtility i (θ i) a| ≤ 1
  dsimp [setup, VCGSetup.trueUtility, VCGSetup.vcgPayment]
  fin_cases i <;>
    cases hθ0 : θ 0 <;> cases hθ1 : θ 1 <;>
    cases ha0 : a 0 <;> cases ha1 : a 1 <;>
    simp [value, allocation, zeroH, hθ0, hθ1, ha0, ha1]

/-- In this concrete witness every report is conforming. The bonus theorem still
applies, and no bonus is paid on the truthful path. -/
def allReportsConform (_i : Buyer) (_a : setup.toInformationalGame.Act _i) :
    Prop :=
  True

theorem truthful_best_response_at_any_reports
    (θ : setup.toInformationalGame.SignalProfile) (i : Buyer)
    (a : setup.toInformationalGame.ActionProfile)
    (a' : setup.toInformationalGame.Act i) :
    setup.toInformationalGame.utility θ
        (Function.update a i (setup.truthfulStrategy i (θ i))) i ≥
      setup.toInformationalGame.utility θ (Function.update a i a') i := by
  have h := setup.vcg_truthful (Function.update a i (θ i)) i a'
  simpa [VCGSetup.toInformationalGame, VCGSetup.truthfulStrategy] using h

/-- Non-vacuous concrete instance of the VCG conformance-bonus capstone. -/
theorem truthful_zero_conformanceBonus_implementation :
    setup.toInformationalGame.IsSignalBlindExPostDominantKImplementation
      (setup.toInformationalGame.conformanceBonusTransfer allReportsConform 2)
      setup.truthfulStrategy 0 := by
  refine
    InformationalGame.conformanceBonusTransfer_isSignalBlindExPostDominantKImplementation
      (G := setup.toInformationalGame) (M := 1) (B := 2)
      allReportsConform (hB := by norm_num) ?_ ?_ ?_ ?_ ?_
  · intro θ i
    trivial
  · exact utility_abs_le_one
  · norm_num
  · intro θ i a a' _
    exact truthful_best_response_at_any_reports θ i a a'
  · intro θ i a a' _
    exact truthful_best_response_at_any_reports θ i a a'

end BoundedOneGoodExample

/-! ### Concrete strict VCG conformance witness -/

namespace StrictConformanceExample

/-- Two buyers for the strict conformance-bonus witness. -/
abbrev Buyer := Fin 2

/-- Binary report/type space. In this witness the VCG values are type-independent;
the conformance bonus, not the allocation rule, supplies strictness. -/
abbrev Kind := Bool

/-- A one-good outcome: no sale or the winning buyer. -/
abbrev Outcome := Option Buyer

def value (i : Buyer) (_t : Kind) : Outcome → ℝ
  | none => 0
  | some j => if j = i then 1 else 0

/-- Efficient tie-breaking toward buyer `0`. Since reported values are
type-independent, either buyer allocation maximizes surplus. -/
def allocation (_report : Buyer → Kind) : Outcome :=
  some 0

theorem allocation_efficient :
    ∀ report o, (∑ i : Buyer, value i (report i) (allocation report)) ≥
      ∑ i : Buyer, value i (report i) o := by
  intro report o
  cases o with
  | none => norm_num [Fin.sum_univ_two, value, allocation]
  | some j =>
      fin_cases j <;> norm_num [Fin.sum_univ_two, value, allocation]

def zeroH (_i : Buyer) (_report : Buyer → Kind) : ℝ :=
  0

theorem zeroH_independent :
    ∀ i, IndependentOfCoordinate i (zeroH i) := by
  intro i report t
  rfl

/-- A concrete VCG setup whose base utilities are report-independent but
bounded. This keeps the strict conformance-bonus hypotheses transparent. -/
noncomputable def setup : VCGSetup Buyer where
  Θ := fun _ => Kind
  Outcome := Outcome
  val := value
  alloc := allocation
  alloc_efficient := allocation_efficient
  h := zeroH
  h_indep := zeroH_independent

/-- The target strategy always sends the conforming report `true`. -/
def targetStrategy : setup.toInformationalGame.StrategyProfile :=
  fun _ _ => true

/-- The proper conformance predicate: only report `true` conforms. -/
def conformingReport (_i : Buyer) (a : setup.toInformationalGame.Act _i) : Prop :=
  a = true

theorem utility_eq_one
    (θ : setup.toInformationalGame.SignalProfile)
    (a : setup.toInformationalGame.ActionProfile) (i : Buyer) :
    setup.toInformationalGame.utility θ a i = 1 := by
  change setup.trueUtility i (θ i) a = 1
  dsimp [setup, VCGSetup.trueUtility, VCGSetup.vcgPayment]
  fin_cases i <;> simp [value, allocation, zeroH]

theorem utility_abs_le_one
    (θ : setup.toInformationalGame.SignalProfile)
    (a : setup.toInformationalGame.ActionProfile) (i : Buyer) :
    |setup.toInformationalGame.utility θ a i| ≤ 1 := by
  rw [utility_eq_one]
  norm_num

def offPathAction (i : Buyer) : setup.toInformationalGame.ActionProfile :=
  Function.update (fun _ : Buyer => false) i true

/-- The strict witness is genuinely non-inert: a conforming player is paid when
the other player sends the nonconforming report. -/
theorem conformanceBonus_fires (i : Buyer) :
    setup.toInformationalGame.conformanceBonusTransfer conformingReport 3
      (offPathAction i) i = 3 := by
  classical
  rw [InformationalGame.conformanceBonusTransfer]
  apply if_pos
  constructor
  · simp [conformingReport, offPathAction]
  · fin_cases i
    · refine ⟨1, by norm_num, ?_⟩
      simp [conformingReport, offPathAction]
    · refine ⟨0, by norm_num, ?_⟩
      simp [conformingReport, offPathAction]

theorem target_best_response
    (θ : setup.toInformationalGame.SignalProfile) (i : Buyer)
    (a : setup.toInformationalGame.ActionProfile)
    (a' : setup.toInformationalGame.Act i) :
    setup.toInformationalGame.utility θ
        (Function.update a i (targetStrategy i (θ i))) i ≥
      setup.toInformationalGame.utility θ (Function.update a i a') i := by
  rw [utility_eq_one, utility_eq_one]

theorem strict_conforming_deviation
    (i : Buyer) (si : setup.toInformationalGame.Signal i)
    (a' : setup.toInformationalGame.Act i) :
    conformingReport i a' → a' ≠ targetStrategy i si →
      ∃ (θ : setup.toInformationalGame.SignalProfile)
        (a : setup.toInformationalGame.ActionProfile), θ i = si ∧
          setup.toInformationalGame.utility θ
              (Function.update a i (targetStrategy i si)) i >
            setup.toInformationalGame.utility θ (Function.update a i a') i := by
  intro ha' hne
  exact False.elim (hne (by simpa [conformingReport, targetStrategy] using ha'))

theorem opponent_nonconforming :
    ∀ i : Buyer, ∃ j : Buyer, j ≠ i ∧
      ∃ a : setup.toInformationalGame.Act j, ¬ conformingReport j a := by
  intro i
  fin_cases i
  · refine ⟨1, by norm_num, false, ?_⟩
    simp [conformingReport]
  · refine ⟨0, by norm_num, false, ?_⟩
    simp [conformingReport]

/-- Concrete strict VCG-side conformance-bonus implementation with a proper
conformance predicate. Unlike `BoundedOneGoodExample`, the bonus has off-path
profiles on which it pays. -/
theorem target_strict_conformanceBonus_implementation :
    setup.toInformationalGame.IsSignalBlindKImplementation
      (setup.toInformationalGame.conformanceBonusTransfer conformingReport 3)
      ({targetStrategy} : Set setup.toInformationalGame.StrategyProfile) 0 := by
  refine
    InformationalGame.conformanceBonusTransfer_isSignalBlindKImplementation_of_strict
      (G := setup.toInformationalGame) (M := 1) (B := 3)
      conformingReport (hB := by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro θ i
    simp [conformingReport, targetStrategy]
  · intro i si
    exact ⟨Function.update (fun _ : Buyer => false) i si, by simp⟩
  · exact utility_abs_le_one
  · norm_num
  · norm_num
  · intro θ i a a' _ha'
    exact target_best_response θ i a a'
  · intro θ i a a' _hopp
    exact target_best_response θ i a a'
  · exact strict_conforming_deviation
  · exact opponent_nonconforming

end StrictConformanceExample

/-! ### Concrete strict frugal VCG witness -/

namespace StrictFrugalVCGExample

/-- Two buyers are enough for a nontrivial quasi-field witness. -/
abbrev Buyer := Fin 2

/-- Two goods make the trivial quasi-field proper, so non-`Q`-based reports
exist. -/
abbrev Good := Fin 2

/-- We use valuations bounded by `1`. -/
abbrev Mbar : ℝ := 1

/-- The trivial quasi-field `{∅, A}` on two goods. -/
def trivialQ : Finset (Finset Good) := {∅, Finset.univ}

@[simp] theorem trivialQ_empty : (∅ : Finset Good) ∈ trivialQ := by
  simp [trivialQ]

@[simp] theorem trivialQ_univ : (Finset.univ : Finset Good) ∈ trivialQ := by
  simp [trivialQ]

theorem trivialQ_isQuasiField : IsQuasiField (A := Good) trivialQ := by
  classical
  simp [IsQuasiField, trivialQ]

theorem feasibleBundles_trivialQ_of_ne_univ {B : Finset Good}
    (hB : B ≠ Finset.univ) :
    Valuation.feasibleBundles trivialQ B = {∅} := by
  classical
  have hnot : ¬ Finset.univ ⊆ B := by
    intro hsub
    exact hB (Finset.eq_univ_of_forall fun x => hsub (by simp))
  ext C
  constructor
  · intro hC
    rcases Finset.mem_filter.mp hC with ⟨hCQ, hCB⟩
    change C ∈ ({∅, Finset.univ} : Finset (Finset Good)) at hCQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hCQ
    rcases hCQ with rfl | hCu
    · simp
    · exact False.elim (hnot (by simpa [hCu] using hCB))
  · intro hC
    have hCempty : C = ∅ := by
      simpa using hC
    subst hCempty
    simp [Valuation.feasibleBundles, trivialQ]

theorem qBasedReport_zero_of_ne_univ {i : Buyer} {v : BoundedValuation Good Mbar}
    (hbased : boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty i v)
    {B : Finset Good} (hB : B ≠ Finset.univ) :
    v B = 0 := by
  classical
  have hb := hbased B
  rw [← hb, Valuation.bundling_value_eq_sup]
  simp [feasibleBundles_trivialQ_of_ne_univ hB]

theorem qBasedReport_ext {i : Buyer} {v w : BoundedValuation Good Mbar}
    (hv : boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty i v)
    (hw : boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty i w)
    (huniv : v Finset.univ = w Finset.univ) :
    v = w := by
  apply Subtype.ext
  ext B
  by_cases hB : B = Finset.univ
  · subst hB
    exact huniv
  · rw [qBasedReport_zero_of_ne_univ (i := i) hv hB,
      qBasedReport_zero_of_ne_univ (i := i) hw hB]

theorem bounded_univ_nonneg (v : BoundedValuation Good Mbar) :
    0 ≤ v Finset.univ :=
  v.nonneg Finset.univ

theorem bounded_univ_le_one (v : BoundedValuation Good Mbar) :
    v Finset.univ ≤ 1 :=
  v.bound Finset.univ

noncomputable def allOrNothingVal (t : ℝ) (h0 : 0 ≤ t) : Valuation Good :=
  Valuation.thresholdBundle (Finset.univ : Finset Good) (by simp) t h0

@[simp] theorem allOrNothingVal_univ (t : ℝ) (h0 : 0 ≤ t) :
    allOrNothingVal t h0 Finset.univ = t := by
  simp [allOrNothingVal]

theorem allOrNothingVal_of_ne_univ (t : ℝ) (h0 : 0 ≤ t)
    {B : Finset Good} (hB : B ≠ Finset.univ) :
    allOrNothingVal t h0 B = 0 := by
  classical
  have hnot : ¬ (Finset.univ : Finset Good) ⊆ B := by
    intro hsub
    exact hB (Finset.eq_univ_of_forall fun x => hsub (by simp))
  exact Valuation.thresholdBundle_apply_of_not_subset hnot

noncomputable def allOrNothingReport (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    BoundedValuation Good Mbar :=
  ⟨allOrNothingVal t h0, by
    intro B
    by_cases hB : B = Finset.univ
    · subst hB
      simpa using h1
    · rw [allOrNothingVal_of_ne_univ t h0 hB]
      norm_num⟩

@[simp] theorem allOrNothingReport_univ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    allOrNothingReport t h0 h1 Finset.univ = t := by
  simp [allOrNothingReport]

theorem allOrNothingReport_of_ne_univ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    {B : Finset Good} (hB : B ≠ Finset.univ) :
    allOrNothingReport t h0 h1 B = 0 := by
  rw [allOrNothingReport, allOrNothingVal_of_ne_univ t h0 hB]

theorem allOrNothingReport_qBased (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty 0
      (allOrNothingReport t h0 h1) := by
  classical
  intro B
  by_cases hB : B = Finset.univ
  · subst hB
    simpa [allOrNothingReport] using
      (Valuation.bundling_eq_original_of_mem (Q := trivialQ)
        trivialQ_empty (v := allOrNothingVal t h0) trivialQ_univ)
  · have hright :
        (allOrNothingReport t h0 h1 : Valuation Good) B = 0 :=
      allOrNothingReport_of_ne_univ t h0 h1 hB
    apply le_antisymm
    · simpa [hright] using
        Valuation.bundling_le_original trivialQ trivialQ_empty
          (allOrNothingReport t h0 h1 : Valuation Good) B
    · rw [hright]
      exact (Valuation.bundling trivialQ trivialQ_empty
        (allOrNothingReport t h0 h1 : Valuation Good)).nonneg B

/-- The frugal surplus-maximizing rule specialized to this two-good bounded
auction. -/
noncomputable abbrev allocation :
    (Buyer → BoundedValuation Good Mbar) → Allocation Buyer Good :=
  boundedFrugalSurplusMaximizingAllocation (ι := Buyer) (A := Good) (M := Mbar)

theorem allocation_isSurplusMaximizer :
    IsBoundedSurplusMaximizer allocation :=
  boundedFrugalSurplusMaximizingAllocation_isSurplusMaximizer
    (ι := Buyer) (A := Good) (M := Mbar)

theorem allocation_isFrugal : IsBoundedFrugal allocation :=
  boundedFrugalSurplusMaximizingAllocation_isFrugal
    (ι := Buyer) (A := Good) (M := Mbar)

def zeroH (_i : Buyer) (_v : Buyer → BoundedValuation Good Mbar) : ℝ := 0

theorem zeroH_independent :
    ∀ i, IndependentOfCoordinate i (zeroH i) := by
  intro i report t
  rfl

noncomputable abbrev setup : VCGSetup Buyer :=
  boundedVcgSetup allocation allocation_isSurplusMaximizer
    zeroH zeroH_independent

noncomputable abbrev game : InformationalGame Buyer :=
  boundedInformationalGame allocation allocation_isSurplusMaximizer
    zeroH zeroH_independent

def zeroVal : Valuation Good where
  value := fun _ => 0
  empty_value := rfl
  monotone := by
    intro B C hBC
    rfl

noncomputable def zeroReport : BoundedValuation Good Mbar :=
  ⟨zeroVal, by
    intro B
    norm_num [zeroVal, Mbar]⟩

@[simp] theorem zeroReport_apply (B : Finset Good) : zeroReport B = 0 := by
  rfl

theorem signal_attainable :
    ∀ i (si : game.Signal i), ∃ θ : game.SignalProfile, θ i = si := by
  intro i si
  exact ⟨Function.update (fun _ : Buyer => zeroReport) i si, by simp⟩

noncomputable def singletonReport : BoundedValuation Good Mbar :=
  ⟨Valuation.thresholdBundle ({0} : Finset Good) (by simp) (1 / 2) (by norm_num),
    by
      intro B
      by_cases h : ({0} : Finset Good) ⊆ B
      · rw [Valuation.thresholdBundle_apply_of_subset h]
        norm_num [Mbar]
      · simp [h]⟩

theorem singletonReport_not_qBased :
    ¬ boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty 0 singletonReport := by
  intro hbased
  have hzero := qBasedReport_zero_of_ne_univ (i := 0) hbased
    (B := ({0} : Finset Good)) (by
      intro h
      have : (1 : Good) ∈ ({0} : Finset Good) := by
        simp [h]
      norm_num at this)
  norm_num [singletonReport] at hzero

theorem opponent_non_qBased :
    ∀ i : Buyer, ∃ j : Buyer, j ≠ i ∧
      ∃ wj : BoundedValuation Good Mbar,
        ¬ boundedQBasedReport trivialQ trivialQ_empty j wj := by
  intro i
  fin_cases i
  · refine ⟨1, by norm_num, singletonReport, ?_⟩
    exact singletonReport_not_qBased
  · refine ⟨0, by norm_num, singletonReport, ?_⟩
    exact singletonReport_not_qBased

theorem utility_abs_le_two (θ : game.SignalProfile) (a : game.ActionProfile)
    (i : Buyer) :
    |game.utility θ a i| ≤ 2 := by
  change |setup.trueUtility i (θ i) a| ≤ 2
  rw [boundedVcgSetup_trueUtility_eq_surplus_update]
  fin_cases i
  · let ar : Buyer → BoundedValuation Good Mbar := a
    let tr : Buyer → BoundedValuation Good Mbar := θ
    change |surplus
        (Function.update
          (fun i : Buyer => ((ar i : BoundedValuation Good Mbar) : Valuation Good))
          0 ((tr 0 : BoundedValuation Good Mbar) : Valuation Good))
        (allocation ar) - 0| ≤ 2
    simp only [surplus, Fin.sum_univ_two, Function.update_apply, ↓reduceIte, sub_zero]
    norm_num
    rw [abs_of_nonneg (add_nonneg
      (BoundedValuation.nonneg (tr 0) ((allocation ar).bundle 0))
      (BoundedValuation.nonneg (ar 1) ((allocation ar).bundle 1)))]
    nlinarith [BoundedValuation.nonneg (tr 0) ((allocation ar).bundle 0),
      BoundedValuation.nonneg (ar 1) ((allocation ar).bundle 1),
      BoundedValuation.bound (tr 0) ((allocation ar).bundle 0),
      BoundedValuation.bound (ar 1) ((allocation ar).bundle 1)]
  · let ar : Buyer → BoundedValuation Good Mbar := a
    let tr : Buyer → BoundedValuation Good Mbar := θ
    change |surplus
        (Function.update
          (fun i : Buyer => ((ar i : BoundedValuation Good Mbar) : Valuation Good))
          1 ((tr 1 : BoundedValuation Good Mbar) : Valuation Good))
        (allocation ar) - 0| ≤ 2
    simp only [surplus, Fin.sum_univ_two, Function.update_apply, ↓reduceIte, sub_zero]
    norm_num
    rw [abs_of_nonneg (add_nonneg
      (BoundedValuation.nonneg (ar 0) ((allocation ar).bundle 0))
      (BoundedValuation.nonneg (tr 1) ((allocation ar).bundle 1)))]
    nlinarith [BoundedValuation.nonneg (ar 0) ((allocation ar).bundle 0),
      BoundedValuation.nonneg (tr 1) ((allocation ar).bundle 1),
      BoundedValuation.bound (ar 0) ((allocation ar).bundle 0),
      BoundedValuation.bound (tr 1) ((allocation ar).bundle 1)]

/-- Allocate all goods to one buyer. -/
def fullTo (i : Buyer) : Allocation Buyer Good where
  bundle j := if j = i then Finset.univ else ∅
  pairwise_disjoint := by
    intro j k hjk
    by_cases hji : j = i
    · by_cases hki : k = i
      · exact False.elim (hjk (hji.trans hki.symm))
      · simpa only [hji, hki, ↓reduceIte] using
          Finset.disjoint_empty_right (s := (Finset.univ : Finset Good))
    · by_cases hki : k = i
      · simpa only [hji, hki, ↓reduceIte] using
          (Finset.disjoint_empty_right (s := (Finset.univ : Finset Good))).symm
      · simpa only [hji, hki, ↓reduceIte] using
          Finset.disjoint_empty_right (s := (∅ : Finset Good))

@[simp] theorem fullTo_bundle_self (i : Buyer) :
    (fullTo i).bundle i = Finset.univ := by
  simp [fullTo]

@[simp] theorem fullTo_bundle_ne {i j : Buyer} (hji : j ≠ i) :
    (fullTo i).bundle j = ∅ := by
  simp [fullTo, hji]

theorem surplus_fullTo_zero
    (v0 v1 : BoundedValuation Good Mbar) :
    surplus (fun i : Buyer => ((![v0, v1] i : BoundedValuation Good Mbar) :
        Valuation Good)) (fullTo 0) = v0 Finset.univ := by
  simp [surplus, Fin.sum_univ_two]

theorem surplus_fullTo_one
    (v0 v1 : BoundedValuation Good Mbar) :
    surplus (fun i : Buyer => ((![v0, v1] i : BoundedValuation Good Mbar) :
        Valuation Good)) (fullTo 1) = v1 Finset.univ := by
  simp [surplus, Fin.sum_univ_two]

theorem eq_empty_of_disjoint_univ {B : Finset Good}
    (h : Disjoint B (Finset.univ : Finset Good)) : B = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (Finset.disjoint_left.mp h) hx (by simp)

theorem bundled_trueUtility_zero_ge_max
    (θ a : Buyer → BoundedValuation Good Mbar) :
    max ((θ 0) Finset.univ) ((a 1) Finset.univ) ≤
      setup.trueUtility 0 (θ 0)
        (Function.update a 0
          (BoundedValuation.bundling trivialQ trivialQ_empty (θ 0))) := by
  let b0 := BoundedValuation.bundling trivialQ trivialQ_empty (θ 0)
  let left := Function.update a 0 b0
  let γ := allocation left
  have hreport_le_true :
      surplus (boundedValuationProfile left) γ ≤
        surplus (Function.update (boundedValuationProfile left) 0
          ((θ 0 : BoundedValuation Good Mbar) : Valuation Good)) γ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [left, b0, Function.update_apply, ↓reduceIte]
    norm_num
    exact Valuation.bundling_le_original trivialQ trivialQ_empty
      (θ 0 : Valuation Good) (γ.bundle 0)
  have htrue_eq :
      setup.trueUtility 0 (θ 0) left =
        surplus (Function.update (boundedValuationProfile left) 0
          ((θ 0 : BoundedValuation Good Mbar) : Valuation Good)) γ := by
    rw [boundedVcgSetup_trueUtility_eq_surplus_update]
    change
      surplus (Function.update (boundedValuationProfile left) 0
          ((θ 0 : BoundedValuation Good Mbar) : Valuation Good)) γ -
        zeroH 0 left =
      surplus (Function.update (boundedValuationProfile left) 0
          ((θ 0 : BoundedValuation Good Mbar) : Valuation Good)) γ
    simp only [zeroH, sub_zero]
  have hmax0 := allocation_isSurplusMaximizer left (fullTo 0)
  have hsurp0 :
      surplus (boundedValuationProfile left) (fullTo 0) = (θ 0) Finset.univ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [left, b0, fullTo_bundle_self,
      fullTo_bundle_ne (by norm_num : (1 : Buyer) ≠ 0),
      Function.update_apply, ↓reduceIte]
    norm_num
    simpa [b0, BoundedValuation.bundling] using
      (Valuation.bundling_eq_original_of_mem (Q := trivialQ)
        trivialQ_empty (v := (θ 0 : Valuation Good)) trivialQ_univ)
  have hge0 : (θ 0) Finset.univ ≤ setup.trueUtility 0 (θ 0) left := by
    rw [htrue_eq]
    calc
      (θ 0) Finset.univ = surplus (boundedValuationProfile left) (fullTo 0) :=
        hsurp0.symm
      _ ≤ surplus (boundedValuationProfile left) γ := hmax0
      _ ≤ surplus (Function.update (boundedValuationProfile left) 0
          ((θ 0 : BoundedValuation Good Mbar) : Valuation Good)) γ := hreport_le_true
  have hmax1 := allocation_isSurplusMaximizer left (fullTo 1)
  have hsurp1 :
      surplus (boundedValuationProfile left) (fullTo 1) = (a 1) Finset.univ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [left, b0, fullTo_bundle_self,
      fullTo_bundle_ne (by norm_num : (0 : Buyer) ≠ 1),
      Function.update_apply, ↓reduceIte]
    norm_num
  have hge1 : (a 1) Finset.univ ≤ setup.trueUtility 0 (θ 0) left := by
    rw [htrue_eq]
    calc
      (a 1) Finset.univ = surplus (boundedValuationProfile left) (fullTo 1) :=
        hsurp1.symm
      _ ≤ surplus (boundedValuationProfile left) γ := hmax1
      _ ≤ surplus (Function.update (boundedValuationProfile left) 0
          ((θ 0 : BoundedValuation Good Mbar) : Valuation Good)) γ := hreport_le_true
  exact max_le hge0 hge1

theorem bundled_trueUtility_one_ge_max
    (θ a : Buyer → BoundedValuation Good Mbar) :
    max ((θ 1) Finset.univ) ((a 0) Finset.univ) ≤
      setup.trueUtility 1 (θ 1)
        (Function.update a 1
          (BoundedValuation.bundling trivialQ trivialQ_empty (θ 1))) := by
  let b1 := BoundedValuation.bundling trivialQ trivialQ_empty (θ 1)
  let left := Function.update a 1 b1
  let γ := allocation left
  have hreport_le_true :
      surplus (boundedValuationProfile left) γ ≤
        surplus (Function.update (boundedValuationProfile left) 1
          ((θ 1 : BoundedValuation Good Mbar) : Valuation Good)) γ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [left, b1, Function.update_apply, ↓reduceIte]
    norm_num
    exact Valuation.bundling_le_original trivialQ trivialQ_empty
      (θ 1 : Valuation Good) (γ.bundle 1)
  have htrue_eq :
      setup.trueUtility 1 (θ 1) left =
        surplus (Function.update (boundedValuationProfile left) 1
          ((θ 1 : BoundedValuation Good Mbar) : Valuation Good)) γ := by
    rw [boundedVcgSetup_trueUtility_eq_surplus_update]
    change
      surplus (Function.update (boundedValuationProfile left) 1
          ((θ 1 : BoundedValuation Good Mbar) : Valuation Good)) γ -
        zeroH 1 left =
      surplus (Function.update (boundedValuationProfile left) 1
          ((θ 1 : BoundedValuation Good Mbar) : Valuation Good)) γ
    simp only [zeroH, sub_zero]
  have hmax1 := allocation_isSurplusMaximizer left (fullTo 1)
  have hsurp1 :
      surplus (boundedValuationProfile left) (fullTo 1) = (θ 1) Finset.univ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [left, b1, fullTo_bundle_self,
      fullTo_bundle_ne (by norm_num : (0 : Buyer) ≠ 1),
      Function.update_apply, ↓reduceIte]
    norm_num
    simpa [b1, BoundedValuation.bundling] using
      (Valuation.bundling_eq_original_of_mem (Q := trivialQ)
        trivialQ_empty (v := (θ 1 : Valuation Good)) trivialQ_univ)
  have hge1 : (θ 1) Finset.univ ≤ setup.trueUtility 1 (θ 1) left := by
    rw [htrue_eq]
    calc
      (θ 1) Finset.univ = surplus (boundedValuationProfile left) (fullTo 1) :=
        hsurp1.symm
      _ ≤ surplus (boundedValuationProfile left) γ := hmax1
      _ ≤ surplus (Function.update (boundedValuationProfile left) 1
          ((θ 1 : BoundedValuation Good Mbar) : Valuation Good)) γ := hreport_le_true
  have hmax0 := allocation_isSurplusMaximizer left (fullTo 0)
  have hsurp0 :
      surplus (boundedValuationProfile left) (fullTo 0) = (a 0) Finset.univ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [left, b1, fullTo_bundle_self,
      fullTo_bundle_ne (by norm_num : (1 : Buyer) ≠ 0),
      Function.update_apply, ↓reduceIte]
    norm_num
  have hge0 : (a 0) Finset.univ ≤ setup.trueUtility 1 (θ 1) left := by
    rw [htrue_eq]
    calc
      (a 0) Finset.univ = surplus (boundedValuationProfile left) (fullTo 0) :=
        hsurp0.symm
      _ ≤ surplus (boundedValuationProfile left) γ := hmax0
      _ ≤ surplus (Function.update (boundedValuationProfile left) 1
          ((θ 1 : BoundedValuation Good Mbar) : Valuation Good)) γ := hreport_le_true
  exact max_le hge1 hge0

noncomputable abbrev targetStrategy : game.StrategyProfile :=
  boundedBundledTruthfulStrategy allocation allocation_isSurplusMaximizer
    zeroH zeroH_independent trivialQ trivialQ_empty

theorem trueUtility_zero_le_opponent_of_report_lt
    (vi own opp : BoundedValuation Good Mbar)
    (hopp : boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty 1 opp)
    (hlt : own Finset.univ < opp Finset.univ) :
    setup.trueUtility 0 vi ![own, opp] ≤ opp Finset.univ := by
  let report : Buyer → BoundedValuation Good Mbar := ![own, opp]
  let γ := allocation report
  have hmax1 := allocation_isSurplusMaximizer report (fullTo 1)
  have hfullTo1 :
      surplus (boundedValuationProfile report) (fullTo 1) = opp Finset.univ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [report, Matrix.cons_val_zero, Matrix.cons_val_one,
      fullTo_bundle_self, fullTo_bundle_ne (by norm_num : (0 : Buyer) ≠ 1)]
    rw [Valuation.empty, zero_add]
  have hγ_report_ge : opp Finset.univ ≤ surplus (boundedValuationProfile report) γ := by
    rw [← hfullTo1]
    exact hmax1
  have hγ1full : γ.bundle 1 = Finset.univ := by
    by_contra hnot
    have hγ_report_le_own : surplus (boundedValuationProfile report) γ ≤ own Finset.univ := by
      unfold surplus boundedValuationProfile
      rw [Fin.sum_univ_two]
      simp only [report, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [qBasedReport_zero_of_ne_univ hopp hnot, add_zero]
      exact (own : Valuation Good).mono (by simp)
    linarith
  have h0empty : γ.bundle 0 = ∅ := by
    apply eq_empty_of_disjoint_univ
    simpa [hγ1full] using γ.pairwise_disjoint (by norm_num : (0 : Buyer) ≠ 1)
  rw [boundedVcgSetup_trueUtility_eq_surplus_update]
  change surplus (Function.update (boundedValuationProfile report) 0
      (vi : Valuation Good)) γ - zeroH 0 report ≤ opp Finset.univ
  simp only [zeroH, sub_zero]
  unfold surplus boundedValuationProfile
  rw [Fin.sum_univ_two]
  simp only [Function.update_apply, ↓reduceIte, report, Matrix.cons_val_one]
  rw [h0empty, hγ1full, Valuation.empty, zero_add]
  norm_num

theorem trueUtility_zero_le_true_of_opponent_lt_report
    (vi own opp : BoundedValuation Good Mbar)
    (hown : boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty 0 own)
    (hlt : opp Finset.univ < own Finset.univ) :
    setup.trueUtility 0 vi ![own, opp] ≤ vi Finset.univ := by
  let report : Buyer → BoundedValuation Good Mbar := ![own, opp]
  let γ := allocation report
  have hmax0 := allocation_isSurplusMaximizer report (fullTo 0)
  have hfullTo0 :
      surplus (boundedValuationProfile report) (fullTo 0) = own Finset.univ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [report, Matrix.cons_val_zero, Matrix.cons_val_one,
      fullTo_bundle_self, fullTo_bundle_ne (by norm_num : (1 : Buyer) ≠ 0)]
    rw [Valuation.empty, add_zero]
  have hγ_report_ge : own Finset.univ ≤ surplus (boundedValuationProfile report) γ := by
    rw [← hfullTo0]
    exact hmax0
  have hγ0full : γ.bundle 0 = Finset.univ := by
    by_contra hnot
    have hγ_report_le_opp : surplus (boundedValuationProfile report) γ ≤ opp Finset.univ := by
      unfold surplus boundedValuationProfile
      rw [Fin.sum_univ_two]
      simp only [report, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [qBasedReport_zero_of_ne_univ hown hnot, zero_add]
      exact (opp : Valuation Good).mono (by simp)
    linarith
  have h1empty : γ.bundle 1 = ∅ := by
    apply eq_empty_of_disjoint_univ
    simpa [hγ0full] using γ.pairwise_disjoint (by norm_num : (1 : Buyer) ≠ 0)
  rw [boundedVcgSetup_trueUtility_eq_surplus_update]
  change surplus (Function.update (boundedValuationProfile report) 0
      (vi : Valuation Good)) γ - zeroH 0 report ≤ vi Finset.univ
  simp only [zeroH, sub_zero]
  unfold surplus boundedValuationProfile
  rw [Fin.sum_univ_two]
  simp only [Function.update_apply, ↓reduceIte, report, Matrix.cons_val_one]
  rw [hγ0full, h1empty, Valuation.empty, add_zero]

theorem trueUtility_one_le_opponent_of_report_lt
    (vi own opp : BoundedValuation Good Mbar)
    (hopp : boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty 0 opp)
    (hlt : own Finset.univ < opp Finset.univ) :
    setup.trueUtility 1 vi ![opp, own] ≤ opp Finset.univ := by
  let report : Buyer → BoundedValuation Good Mbar := ![opp, own]
  let γ := allocation report
  have hmax0 := allocation_isSurplusMaximizer report (fullTo 0)
  have hfullTo0 :
      surplus (boundedValuationProfile report) (fullTo 0) = opp Finset.univ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [report, Matrix.cons_val_zero, Matrix.cons_val_one,
      fullTo_bundle_self, fullTo_bundle_ne (by norm_num : (1 : Buyer) ≠ 0)]
    rw [Valuation.empty, add_zero]
  have hγ_report_ge : opp Finset.univ ≤ surplus (boundedValuationProfile report) γ := by
    rw [← hfullTo0]
    exact hmax0
  have hγ0full : γ.bundle 0 = Finset.univ := by
    by_contra hnot
    have hγ_report_le_own : surplus (boundedValuationProfile report) γ ≤ own Finset.univ := by
      unfold surplus boundedValuationProfile
      rw [Fin.sum_univ_two]
      simp only [report, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [qBasedReport_zero_of_ne_univ hopp hnot, zero_add]
      exact (own : Valuation Good).mono (by simp)
    linarith
  have h1empty : γ.bundle 1 = ∅ := by
    apply eq_empty_of_disjoint_univ
    simpa [hγ0full] using γ.pairwise_disjoint (by norm_num : (1 : Buyer) ≠ 0)
  rw [boundedVcgSetup_trueUtility_eq_surplus_update]
  change surplus (Function.update (boundedValuationProfile report) 1
      (vi : Valuation Good)) γ - zeroH 1 report ≤ opp Finset.univ
  simp only [zeroH, sub_zero]
  unfold surplus boundedValuationProfile
  rw [Fin.sum_univ_two]
  simp only [Function.update_apply, ↓reduceIte, report, Matrix.cons_val_zero]
  rw [hγ0full, h1empty, Valuation.empty, add_zero]
  norm_num

theorem trueUtility_one_le_true_of_opponent_lt_report
    (vi own opp : BoundedValuation Good Mbar)
    (hown : boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty 1 own)
    (hlt : opp Finset.univ < own Finset.univ) :
    setup.trueUtility 1 vi ![opp, own] ≤ vi Finset.univ := by
  let report : Buyer → BoundedValuation Good Mbar := ![opp, own]
  let γ := allocation report
  have hmax1 := allocation_isSurplusMaximizer report (fullTo 1)
  have hfullTo1 :
      surplus (boundedValuationProfile report) (fullTo 1) = own Finset.univ := by
    unfold surplus boundedValuationProfile
    rw [Fin.sum_univ_two]
    simp only [report, Matrix.cons_val_zero, Matrix.cons_val_one,
      fullTo_bundle_self, fullTo_bundle_ne (by norm_num : (0 : Buyer) ≠ 1)]
    rw [Valuation.empty, zero_add]
  have hγ_report_ge : own Finset.univ ≤ surplus (boundedValuationProfile report) γ := by
    rw [← hfullTo1]
    exact hmax1
  have hγ1full : γ.bundle 1 = Finset.univ := by
    by_contra hnot
    have hγ_report_le_opp : surplus (boundedValuationProfile report) γ ≤ opp Finset.univ := by
      unfold surplus boundedValuationProfile
      rw [Fin.sum_univ_two]
      simp only [report, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [qBasedReport_zero_of_ne_univ hown hnot, add_zero]
      exact (opp : Valuation Good).mono (by simp)
    linarith
  have h0empty : γ.bundle 0 = ∅ := by
    apply eq_empty_of_disjoint_univ
    simpa [hγ1full] using γ.pairwise_disjoint (by norm_num : (0 : Buyer) ≠ 1)
  rw [boundedVcgSetup_trueUtility_eq_surplus_update]
  change surplus (Function.update (boundedValuationProfile report) 1
      (vi : Valuation Good)) γ - zeroH 1 report ≤ vi Finset.univ
  simp only [zeroH, sub_zero]
  unfold surplus boundedValuationProfile
  rw [Fin.sum_univ_two]
  simp only [Function.update_apply, ↓reduceIte, report, Matrix.cons_val_zero]
  rw [h0empty, hγ1full, Valuation.empty, zero_add]

theorem strict_qBased_deviation :
    ∀ (i : Buyer) (vi wi : BoundedValuation Good Mbar),
      boundedQBasedReport trivialQ trivialQ_empty i wi →
        wi ≠ BoundedValuation.bundling trivialQ trivialQ_empty vi →
          ∃ (θ : game.SignalProfile) (a : game.ActionProfile), θ i = vi ∧
            game.utility θ (Function.update a i (targetStrategy i vi)) i >
              game.utility θ (Function.update a i wi) i := by
  intro i vi wi hwi hne
  fin_cases i
  · have hneq : wi Finset.univ ≠ vi Finset.univ := by
      intro heq
      apply hne
      apply qBasedReport_ext (i := 0) hwi
      · exact BoundedValuation.bundling_isBasedOn trivialQ trivialQ_empty vi
      · calc
          wi Finset.univ = vi Finset.univ := heq
          _ = (BoundedValuation.bundling trivialQ trivialQ_empty vi) Finset.univ := by
            symm
            simpa [BoundedValuation.bundling] using
              (Valuation.bundling_eq_original_of_mem (Q := trivialQ)
                trivialQ_empty (v := (vi : Valuation Good)) trivialQ_univ)
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · let m : ℝ := (wi Finset.univ + vi Finset.univ) / 2
      have hm0 : 0 ≤ m := by
        have hwi0 := bounded_univ_nonneg wi
        have hvi0 := bounded_univ_nonneg vi
        dsimp [m]
        linarith
      have hm1 : m ≤ 1 := by
        have hwi1 := bounded_univ_le_one wi
        have hvi1 := bounded_univ_le_one vi
        dsimp [m]
        linarith
      let mid := allOrNothingReport m hm0 hm1
      let θ : Buyer → BoundedValuation Good Mbar :=
        Function.update (fun _ : Buyer => zeroReport) 0 vi
      let a : Buyer → BoundedValuation Good Mbar := ![zeroReport, mid]
      refine ⟨θ, a, by simp [θ], ?_⟩
      have hmidQ : boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty 1 mid :=
        allOrNothingReport_qBased m hm0 hm1
      have hleft_ge := bundled_trueUtility_zero_ge_max θ a
      have hleft_ge_vi : vi Finset.univ ≤ setup.trueUtility 0 vi
          (Function.update a 0 (BoundedValuation.bundling trivialQ trivialQ_empty vi)) := by
        exact le_trans (le_max_left (vi Finset.univ) (mid Finset.univ)) hleft_ge
      have hright_le := trueUtility_zero_le_opponent_of_report_lt vi wi mid hmidQ (by
        dsimp [mid, m]
        rw [allOrNothingReport_univ]
        linarith)
      have hm_lt_vi : mid Finset.univ < vi Finset.univ := by
        dsimp [mid, m]
        rw [allOrNothingReport_univ]
        linarith
      change setup.trueUtility 0 vi
          (Function.update a 0 (BoundedValuation.bundling trivialQ trivialQ_empty vi)) >
        setup.trueUtility 0 vi ![wi, mid]
      linarith
    · let m : ℝ := (wi Finset.univ + vi Finset.univ) / 2
      have hm0 : 0 ≤ m := by
        have hwi0 := bounded_univ_nonneg wi
        have hvi0 := bounded_univ_nonneg vi
        dsimp [m]
        linarith
      have hm1 : m ≤ 1 := by
        have hwi1 := bounded_univ_le_one wi
        have hvi1 := bounded_univ_le_one vi
        dsimp [m]
        linarith
      let mid := allOrNothingReport m hm0 hm1
      let θ : Buyer → BoundedValuation Good Mbar :=
        Function.update (fun _ : Buyer => zeroReport) 0 vi
      let a : Buyer → BoundedValuation Good Mbar := ![zeroReport, mid]
      refine ⟨θ, a, by simp [θ], ?_⟩
      have hleft_ge := bundled_trueUtility_zero_ge_max θ a
      have hleft_ge_mid : mid Finset.univ ≤ setup.trueUtility 0 vi
          (Function.update a 0 (BoundedValuation.bundling trivialQ trivialQ_empty vi)) := by
        exact le_trans (le_max_right (vi Finset.univ) (mid Finset.univ)) hleft_ge
      have hright_le := trueUtility_zero_le_true_of_opponent_lt_report vi wi mid hwi (by
        dsimp [mid, m]
        rw [allOrNothingReport_univ]
        linarith)
      have hvi_lt_mid : vi Finset.univ < mid Finset.univ := by
        dsimp [mid, m]
        rw [allOrNothingReport_univ]
        linarith
      change setup.trueUtility 0 vi
          (Function.update a 0 (BoundedValuation.bundling trivialQ trivialQ_empty vi)) >
        setup.trueUtility 0 vi ![wi, mid]
      linarith
  · have hneq : wi Finset.univ ≠ vi Finset.univ := by
      intro heq
      apply hne
      apply qBasedReport_ext (i := 1) hwi
      · exact BoundedValuation.bundling_isBasedOn trivialQ trivialQ_empty vi
      · calc
          wi Finset.univ = vi Finset.univ := heq
          _ = (BoundedValuation.bundling trivialQ trivialQ_empty vi) Finset.univ := by
            symm
            simpa [BoundedValuation.bundling] using
              (Valuation.bundling_eq_original_of_mem (Q := trivialQ)
                trivialQ_empty (v := (vi : Valuation Good)) trivialQ_univ)
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · let m : ℝ := (wi Finset.univ + vi Finset.univ) / 2
      have hm0 : 0 ≤ m := by
        have hwi0 := bounded_univ_nonneg wi
        have hvi0 := bounded_univ_nonneg vi
        dsimp [m]
        linarith
      have hm1 : m ≤ 1 := by
        have hwi1 := bounded_univ_le_one wi
        have hvi1 := bounded_univ_le_one vi
        dsimp [m]
        linarith
      let mid := allOrNothingReport m hm0 hm1
      let θ : Buyer → BoundedValuation Good Mbar :=
        Function.update (fun _ : Buyer => zeroReport) 1 vi
      let a : Buyer → BoundedValuation Good Mbar := ![mid, zeroReport]
      refine ⟨θ, a, by simp [θ], ?_⟩
      have hmidQ : boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty 0 mid :=
        allOrNothingReport_qBased m hm0 hm1
      have hleft_ge := bundled_trueUtility_one_ge_max θ a
      have hleft_ge_vi : vi Finset.univ ≤ setup.trueUtility 1 vi
          (Function.update a 1 (BoundedValuation.bundling trivialQ trivialQ_empty vi)) := by
        exact le_trans (le_max_left (vi Finset.univ) (mid Finset.univ)) hleft_ge
      have hright_le := trueUtility_one_le_opponent_of_report_lt vi wi mid hmidQ (by
        dsimp [mid, m]
        rw [allOrNothingReport_univ]
        linarith)
      have hm_lt_vi : mid Finset.univ < vi Finset.univ := by
        dsimp [mid, m]
        rw [allOrNothingReport_univ]
        linarith
      change setup.trueUtility 1 vi
          (Function.update a 1 (BoundedValuation.bundling trivialQ trivialQ_empty vi)) >
        setup.trueUtility 1 vi ![mid, wi]
      linarith
    · let m : ℝ := (wi Finset.univ + vi Finset.univ) / 2
      have hm0 : 0 ≤ m := by
        have hwi0 := bounded_univ_nonneg wi
        have hvi0 := bounded_univ_nonneg vi
        dsimp [m]
        linarith
      have hm1 : m ≤ 1 := by
        have hwi1 := bounded_univ_le_one wi
        have hvi1 := bounded_univ_le_one vi
        dsimp [m]
        linarith
      let mid := allOrNothingReport m hm0 hm1
      let θ : Buyer → BoundedValuation Good Mbar :=
        Function.update (fun _ : Buyer => zeroReport) 1 vi
      let a : Buyer → BoundedValuation Good Mbar := ![mid, zeroReport]
      refine ⟨θ, a, by simp [θ], ?_⟩
      have hleft_ge := bundled_trueUtility_one_ge_max θ a
      have hleft_ge_mid : mid Finset.univ ≤ setup.trueUtility 1 vi
          (Function.update a 1 (BoundedValuation.bundling trivialQ trivialQ_empty vi)) := by
        exact le_trans (le_max_right (vi Finset.univ) (mid Finset.univ)) hleft_ge
      have hright_le := trueUtility_one_le_true_of_opponent_lt_report vi wi mid hwi (by
        dsimp [mid, m]
        rw [allOrNothingReport_univ]
        linarith)
      have hvi_lt_mid : vi Finset.univ < mid Finset.univ := by
        dsimp [mid, m]
        rw [allOrNothingReport_univ]
        linarith
      change setup.trueUtility 1 vi
          (Function.update a 1 (BoundedValuation.bundling trivialQ trivialQ_empty vi)) >
        setup.trueUtility 1 vi ![mid, wi]
      linarith

/-- A concrete non-vacuous instance of the strict frugal-VCG theorem.

Two buyers compete for two goods under the quasi-field `{∅, A}`. The allocation
rule is the frugal surplus-maximizing selector; the strict separation
hypothesis is witnessed by midpoint all-or-nothing opponent bids. -/
theorem strict_frugal_vcg_implementation :
    game.IsSignalBlindKImplementation
      (game.conformanceBonusTransfer
        (boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty) 5)
      ({targetStrategy} : Set game.StrategyProfile) 0 := by
  exact
    boundedConformanceBonusTransfer_bundledTruthful_isSignalBlindKImplementation_of_strict
      (d := allocation) (hd := allocation_isSurplusMaximizer)
      (hfrugal := allocation_isFrugal)
      (h := zeroH) (hh := zeroH_independent)
      (hQ := trivialQ_isQuasiField)
      (M := 2) (B := 5)
      (hB := by norm_num)
      signal_attainable
      utility_abs_le_two
      (by norm_num)
      (by norm_num)
      strict_qBased_deviation
      opponent_non_qBased

end StrictFrugalVCGExample

/- The four-good example after Lemma 1: without frugality, a `Q`-based
deviation can beat the bundled report. -/
namespace FrugalityNecessityExample

abbrev Buyer := Fin 2
abbrev Good := Fin 4

def ab : Finset Good := {0, 1}
def cd : Finset Good := {2, 3}
def abc : Finset Good := {0, 1, 2}
def dBundle : Finset Good := {3}
def abcd : Finset Good := ab ∪ cd

def sigma : Finset (Finset Good) := {∅, ab, cd, abcd}

theorem sigma_empty : (∅ : Finset Good) ∈ sigma := by
  simp [sigma]

theorem sigma_ab : ab ∈ sigma := by
  simp [sigma]

theorem sigma_cd : cd ∈ sigma := by
  simp [sigma]

theorem sigma_abcd : abcd ∈ sigma := by
  simp [sigma]

def threshold (S B : Finset Good) (w : ℝ) : ℝ :=
  if S ⊆ B then w else 0

theorem threshold_mono {S B C : Finset Good} {w : ℝ} (hw : 0 ≤ w)
    (hBC : B ⊆ C) :
    threshold S B w ≤ threshold S C w := by
  unfold threshold
  by_cases hSB : S ⊆ B
  · have hSC : S ⊆ C := hSB.trans hBC
    simp [hSB, hSC]
  · by_cases hSC : S ⊆ C
    · simp [hSB, hSC, hw]
    · simp [hSB, hSC]

noncomputable def v1 : Valuation Good where
  value B := threshold ab B 1 + threshold abc B (1 / 10)
  empty_value := by
    norm_num [threshold, ab, abc]
  monotone := by
    intro B C hBC
    have hab := threshold_mono (S := ab) (w := (1 : ℝ)) (by norm_num) hBC
    have habc := threshold_mono (S := abc) (w := (1 / 10 : ℝ)) (by norm_num) hBC
    linarith

noncomputable def vhat2 : Valuation Good where
  value B := threshold dBundle B (3 / 4)
  empty_value := by
    norm_num [threshold, dBundle]
  monotone := by
    intro B C hBC
    exact threshold_mono (S := dBundle) (w := (3 / 4 : ℝ)) (by norm_num) hBC

noncomputable def w1 : Valuation Good where
  value B := threshold ab B 1 + threshold cd B (1 / 10)
  empty_value := by
    norm_num [threshold, ab, cd]
  monotone := by
    intro B C hBC
    have hab := threshold_mono (S := ab) (w := (1 : ℝ)) (by norm_num) hBC
    have hcd := threshold_mono (S := cd) (w := (1 / 10 : ℝ)) (by norm_num) hBC
    linarith

noncomputable def v1Sigma : Valuation Good :=
  Valuation.bundling sigma sigma_empty v1

@[simp] theorem v1_ab : v1 ab = 1 := by
  have hnot : ¬ abc ⊆ ab := by decide
  simp [v1, threshold, hnot]

@[simp] theorem v1_abc : v1 abc = 11 / 10 := by
  norm_num [v1, threshold, ab, abc]

@[simp] theorem vhat2_cd : vhat2 cd = 3 / 4 := by
  norm_num [vhat2, threshold, cd, dBundle]

@[simp] theorem vhat2_dBundle : vhat2 dBundle = 3 / 4 := by
  norm_num [vhat2, threshold, dBundle]

@[simp] theorem w1_ab : w1 ab = 1 := by
  have hnot : ¬ cd ⊆ ab := by decide
  simp [w1, threshold, hnot]

@[simp] theorem w1_abc : w1 abc = 1 := by
  have hab : ab ⊆ abc := by decide
  have hnot : ¬ cd ⊆ abc := by decide
  simp [w1, threshold, hab, hnot]

@[simp] theorem w1_cd : w1 cd = 1 / 10 := by
  have hnot : ¬ ab ⊆ cd := by decide
  simp [w1, threshold, hnot]

@[simp] theorem v1Sigma_ab : v1Sigma ab = 1 := by
  rw [v1Sigma, Valuation.bundling_eq_original_of_mem
    (Q := sigma) sigma_empty (v := v1) sigma_ab]
  simp

@[simp] theorem v1Sigma_cd : v1Sigma cd = 0 := by
  rw [v1Sigma, Valuation.bundling_eq_original_of_mem
    (Q := sigma) sigma_empty (v := v1) sigma_cd]
  have hnot_ab : ¬ ab ⊆ cd := by decide
  have hnot_abc : ¬ abc ⊆ cd := by decide
  simp [v1, threshold, hnot_ab, hnot_abc]

theorem w1_isSigmaBased :
    Valuation.IsBasedOn sigma sigma_empty w1 := by
  intro B
  apply le_antisymm
  · exact Valuation.bundling_le_original sigma sigma_empty w1 B
  · by_cases hab : ab ⊆ B
    · by_cases hcd : cd ⊆ B
      · have habcd_subset : abcd ⊆ B := by
          rw [abcd]
          exact Finset.union_subset hab hcd
        have hval : w1 B = w1 abcd := by
          have hab_abcd : ab ⊆ abcd := by simp [abcd]
          have hcd_abcd : cd ⊆ abcd := by simp [abcd]
          simp [w1, threshold, hab, hcd, hab_abcd, hcd_abcd]
        rw [hval]
        exact Valuation.le_bundling_of_mem (Q := sigma) sigma_empty
          (v := w1) sigma_abcd habcd_subset
      · have hval : w1 B = w1 ab := by
          have hnot_cd_ab : ¬ cd ⊆ ab := by decide
          simp [w1, threshold, hab, hcd, hnot_cd_ab]
        rw [hval]
        exact Valuation.le_bundling_of_mem (Q := sigma) sigma_empty
          (v := w1) sigma_ab hab
    · by_cases hcd : cd ⊆ B
      · have hval : w1 B = w1 cd := by
          have hnot_ab_cd : ¬ ab ⊆ cd := by decide
          simp [w1, threshold, hab, hcd, hnot_ab_cd]
        rw [hval]
        exact Valuation.le_bundling_of_mem (Q := sigma) sigma_empty
          (v := w1) sigma_cd hcd
      · have hval : w1 B = w1 (∅ : Finset Good) := by
          simp [w1, threshold, hab, hcd]
        rw [hval]
        exact Valuation.le_bundling_of_mem (Q := sigma) sigma_empty
          (v := w1) sigma_empty (by simp)

def report (v₀ v₁ : Valuation Good) : Buyer → Valuation Good
  | 0 => v₀
  | 1 => v₁

noncomputable def truthfulReport : Buyer → Valuation Good :=
  report v1Sigma vhat2

noncomputable def cheatingReport : Buyer → Valuation Good :=
  report w1 vhat2

theorem truthfulReport_ne_cheatingReport :
    truthfulReport ≠ cheatingReport := by
  intro h
  have h0 : truthfulReport 0 = cheatingReport 0 := congrFun h 0
  have hcd := congrArg (fun v : Valuation Good => v cd) h0
  norm_num [truthfulReport, cheatingReport, report] at hcd

def truthfulAllocation : Allocation Buyer Good where
  bundle
    | 0 => ab
    | 1 => cd
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [ab, cd] at hij ⊢

def cheatingAllocation : Allocation Buyer Good where
  bundle
    | 0 => abc
    | 1 => dBundle
  pairwise_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [abc, dBundle] at hij ⊢

@[simp] theorem truthfulAllocation_bundle_zero :
    truthfulAllocation.bundle 0 = ab := rfl

@[simp] theorem truthfulAllocation_bundle_one :
    truthfulAllocation.bundle 1 = cd := rfl

@[simp] theorem cheatingAllocation_bundle_zero :
    cheatingAllocation.bundle 0 = abc := rfl

@[simp] theorem cheatingAllocation_bundle_one :
    cheatingAllocation.bundle 1 = dBundle := rfl

theorem truthfulAllocation_surplus :
    surplus truthfulReport truthfulAllocation = 7 / 4 := by
  norm_num [surplus, truthfulReport, report]

theorem cheatingAllocation_surplus :
    surplus cheatingReport cheatingAllocation = 7 / 4 := by
  norm_num [surplus, cheatingReport, report]

theorem v1Sigma_le_eleven_ten (B : Finset Good) :
    v1Sigma B ≤ 11 / 10 := by
  change
    (Valuation.feasibleBundles sigma B).sup'
        (Valuation.feasibleBundles_nonempty sigma_empty B) (fun C => v1 C) ≤
      11 / 10
  apply Finset.sup'_le
  intro C hC
  rcases Finset.mem_filter.mp hC with ⟨hCσ, _⟩
  have hCσ' : C = ∅ ∨ C = ab ∨ C = cd ∨ C = abcd := by
    simpa [sigma] using hCσ
  rcases hCσ' with rfl | rfl | rfl | rfl
  · norm_num [v1, threshold]
  · have hnot : ¬ abc ⊆ ab := by decide
    norm_num [v1, threshold, hnot]
  · have hnot_ab : ¬ ab ⊆ cd := by decide
    have hnot_abc : ¬ abc ⊆ cd := by decide
    norm_num [v1, threshold, hnot_ab, hnot_abc]
  · have hab : ab ⊆ abcd := by simp [abcd]
    have habc : abc ⊆ abcd := by decide
    norm_num [v1, threshold, hab, habc]

theorem v1Sigma_le_one_of_not_abcd {B : Finset Good}
    (hnot : ¬ abcd ⊆ B) :
    v1Sigma B ≤ 1 := by
  change
    (Valuation.feasibleBundles sigma B).sup'
        (Valuation.feasibleBundles_nonempty sigma_empty B) (fun C => v1 C) ≤
      1
  apply Finset.sup'_le
  intro C hC
  rcases Finset.mem_filter.mp hC with ⟨hCσ, hCB⟩
  have hCσ' : C = ∅ ∨ C = ab ∨ C = cd ∨ C = abcd := by
    simpa [sigma] using hCσ
  rcases hCσ' with rfl | rfl | rfl | rfl
  · norm_num [v1, threshold]
  · have hnot : ¬ abc ⊆ ab := by decide
    norm_num [v1, threshold, hnot]
  · have hnot_ab : ¬ ab ⊆ cd := by decide
    have hnot_abc : ¬ abc ⊆ cd := by decide
    norm_num [v1, threshold, hnot_ab, hnot_abc]
  · exact False.elim (hnot hCB)

theorem vhat2_le_three_four (B : Finset Good) :
    vhat2 B ≤ 3 / 4 := by
  change threshold dBundle B (3 / 4) ≤ 3 / 4
  unfold threshold
  split_ifs <;> norm_num

theorem vhat2_eq_zero_of_not_dBundle {B : Finset Good}
    (hnot : ¬ dBundle ⊆ B) :
    vhat2 B = 0 := by
  simp [vhat2, threshold, hnot]

theorem w1_le_eleven_ten (B : Finset Good) :
    w1 B ≤ 11 / 10 := by
  change threshold ab B 1 + threshold cd B (1 / 10) ≤ 11 / 10
  unfold threshold
  split_ifs <;> norm_num

theorem w1_le_one_of_not_cd {B : Finset Good} (hnot : ¬ cd ⊆ B) :
    w1 B ≤ 1 := by
  change threshold ab B 1 + threshold cd B (1 / 10) ≤ 1
  unfold threshold
  by_cases hab : ab ⊆ B <;> by_cases hcd : cd ⊆ B
  · exact False.elim (hnot hcd)
  · norm_num [hab, hcd]
  · norm_num [hab, hcd]
  · norm_num [hab, hcd]

theorem truthfulAllocation_isOptimal :
    surplus truthfulReport truthfulAllocation ≥ surplus truthfulReport γ := by
  have hdis : Disjoint (γ.bundle 0) (γ.bundle 1) :=
    γ.pairwise_disjoint (by decide : (0 : Buyer) ≠ 1)
  rw [truthfulAllocation_surplus]
  simp [surplus, truthfulReport, report]
  by_cases hd : dBundle ⊆ γ.bundle 1
  · have hnot_abcd : ¬ abcd ⊆ γ.bundle 0 := by
      intro habcd
      have hd0 : (3 : Good) ∈ γ.bundle 0 := habcd (by simp [abcd, cd])
      have hd1 : (3 : Good) ∈ γ.bundle 1 := hd (by simp [dBundle])
      exact (Finset.disjoint_left.mp hdis) hd0 hd1
    have h0 := v1Sigma_le_one_of_not_abcd (B := γ.bundle 0) hnot_abcd
    have h1 := vhat2_le_three_four (γ.bundle 1)
    linarith
  · have h0 := v1Sigma_le_eleven_ten (γ.bundle 0)
    have h1 : vhat2 (γ.bundle 1) = 0 :=
      vhat2_eq_zero_of_not_dBundle hd
    linarith

theorem cheatingAllocation_isOptimal :
    surplus cheatingReport cheatingAllocation ≥ surplus cheatingReport γ := by
  have hdis : Disjoint (γ.bundle 0) (γ.bundle 1) :=
    γ.pairwise_disjoint (by decide : (0 : Buyer) ≠ 1)
  rw [cheatingAllocation_surplus]
  simp [surplus, cheatingReport, report]
  by_cases hd : dBundle ⊆ γ.bundle 1
  · have hnot_cd : ¬ cd ⊆ γ.bundle 0 := by
      intro hcd
      have hd0 : (3 : Good) ∈ γ.bundle 0 := hcd (by simp [cd])
      have hd1 : (3 : Good) ∈ γ.bundle 1 := hd (by simp [dBundle])
      exact (Finset.disjoint_left.mp hdis) hd0 hd1
    have h0 := w1_le_one_of_not_cd (B := γ.bundle 0) hnot_cd
    have h1 := vhat2_le_three_four (γ.bundle 1)
    linarith
  · have h0 := w1_le_eleven_ten (γ.bundle 0)
    have h1 : vhat2 (γ.bundle 1) = 0 :=
      vhat2_eq_zero_of_not_dBundle hd
    linarith

/-- Efficient tie-breaking rule for the non-frugality example. It selects the
paper's two displayed optimal allocations at the two displayed reports, and
uses arbitrary surplus-maximizing tie-breaking elsewhere. -/
noncomputable def nonfrugalAllocationRule (v : Buyer → Valuation Good) :
    Allocation Buyer Good :=
  open Classical in
  if _htruth : v = truthfulReport then truthfulAllocation
  else if _hcheat : v = cheatingReport then cheatingAllocation
  else surplusMaximizingAllocation v

@[simp] theorem nonfrugalAllocationRule_truthful :
    nonfrugalAllocationRule truthfulReport = truthfulAllocation := by
  rw [nonfrugalAllocationRule, dif_pos rfl]

@[simp] theorem nonfrugalAllocationRule_cheating :
    nonfrugalAllocationRule cheatingReport = cheatingAllocation := by
  have hne : cheatingReport ≠ truthfulReport := fun h =>
    truthfulReport_ne_cheatingReport h.symm
  rw [nonfrugalAllocationRule, dif_neg hne, dif_pos rfl]

theorem nonfrugalAllocationRule_isSurplusMaximizer :
    IsSurplusMaximizer nonfrugalAllocationRule := by
  intro v γ
  by_cases htruth : v = truthfulReport
  · rw [nonfrugalAllocationRule, dif_pos htruth]
    rw [htruth]
    exact truthfulAllocation_isOptimal
  · by_cases hcheat : v = cheatingReport
    · rw [nonfrugalAllocationRule, dif_neg htruth, dif_pos hcheat]
      rw [hcheat]
      exact cheatingAllocation_isOptimal
    · rw [nonfrugalAllocationRule, dif_neg htruth, dif_neg hcheat]
      exact surplusMaximizingAllocation_isSurplusMaximizer v γ

theorem nonfrugal_witness :
    ab ⊂ cheatingAllocation.bundle 0 ∧
      w1 ab = w1 (cheatingAllocation.bundle 0) := by
  constructor
  · decide
  · simp

theorem nonfrugalAllocationRule_not_frugal :
    ¬ IsFrugal nonfrugalAllocationRule := by
  intro hfrugal
  have hproper :
      ab ⊂ (nonfrugalAllocationRule cheatingReport).bundle 0 := by
    simpa [nonfrugalAllocationRule_cheating] using nonfrugal_witness.1
  have hlt := hfrugal cheatingReport 0 ab hproper
  have heq :
      cheatingReport 0 ab =
        cheatingReport 0 ((nonfrugalAllocationRule cheatingReport).bundle 0) := by
    rw [nonfrugalAllocationRule_cheating]
    simp [cheatingReport, report]
  rw [heq] at hlt
  exact lt_irrefl _ hlt

theorem truthful_bundled_utility :
    v1 (truthfulAllocation.bundle 0) = 1 := by
  simp

theorem cheating_utility :
    v1 (cheatingAllocation.bundle 0) = 11 / 10 := by
  simp

theorem cheating_beats_bundled :
    v1 (truthfulAllocation.bundle 0) < v1 (cheatingAllocation.bundle 0) := by
  norm_num [truthful_bundled_utility, cheating_utility]

def zeroExternality (_i : Buyer) (_v : Buyer → Valuation Good) : ℝ := 0

theorem zeroExternality_independent :
    ∀ i, IndependentOfCoordinate i (zeroExternality i) := by
  intro i v wi
  rfl

noncomputable abbrev nonfrugalVCGSetup : VCGSetup Buyer :=
  vcgSetup nonfrugalAllocationRule nonfrugalAllocationRule_isSurplusMaximizer
    zeroExternality zeroExternality_independent

theorem nonfrugalVCGSetup_trueUtility_bundled :
    nonfrugalVCGSetup.trueUtility 0 v1 truthfulReport = 7 / 4 := by
  rw [vcgSetup_trueUtility_eq_surplus_update]
  rw [nonfrugalAllocationRule_truthful]
  norm_num [nonfrugalVCGSetup, zeroExternality, surplus, truthfulReport,
    report, Function.update]

theorem nonfrugalVCGSetup_trueUtility_cheating :
    nonfrugalVCGSetup.trueUtility 0 v1 cheatingReport = 37 / 20 := by
  rw [vcgSetup_trueUtility_eq_surplus_update]
  rw [nonfrugalAllocationRule_cheating]
  norm_num [nonfrugalVCGSetup, zeroExternality, surplus, cheatingReport,
    report, Function.update]

theorem nonfrugalVCGSetup_cheating_trueUtility_gt_bundled :
    nonfrugalVCGSetup.trueUtility 0 v1 truthfulReport <
      nonfrugalVCGSetup.trueUtility 0 v1 cheatingReport := by
  rw [nonfrugalVCGSetup_trueUtility_bundled,
    nonfrugalVCGSetup_trueUtility_cheating]
  norm_num

/-- Machine-checked version of the paper's post-Lemma-1 example. The two
specified allocations are surplus-maximizing tie-breaks of the reported VC
problems, the second tie-break is non-frugal, and the `sigma`-based deviation
`w1` gives buyer 1 strictly higher true value than reporting `v1Sigma`. -/
theorem lemma1_fails_without_frugality :
    Valuation.IsBasedOn sigma sigma_empty w1 ∧
      surplus truthfulReport truthfulAllocation ≥ surplus truthfulReport γ ∧
      surplus cheatingReport cheatingAllocation ≥ surplus cheatingReport δ ∧
      ab ⊂ cheatingAllocation.bundle 0 ∧
      w1 ab = w1 (cheatingAllocation.bundle 0) ∧
      v1 (truthfulAllocation.bundle 0) <
        v1 (cheatingAllocation.bundle 0) := by
  exact ⟨w1_isSigmaBased, truthfulAllocation_isOptimal,
    cheatingAllocation_isOptimal, nonfrugal_witness.1, nonfrugal_witness.2,
    cheating_beats_bundled⟩

/-- Utility-level version of the post-Lemma-1 example: there is an efficient
VCG tie-break that is not frugal, and under it the `sigma`-based report `w1`
gives buyer 1 strictly greater true VCG utility than the bundled report. -/
theorem lemma1_fails_without_frugality_trueUtility :
    IsSurplusMaximizer nonfrugalAllocationRule ∧
      ¬ IsFrugal nonfrugalAllocationRule ∧
        Valuation.IsBasedOn sigma sigma_empty w1 ∧
          nonfrugalVCGSetup.trueUtility 0 v1 truthfulReport <
            nonfrugalVCGSetup.trueUtility 0 v1 cheatingReport := by
  exact ⟨nonfrugalAllocationRule_isSurplusMaximizer,
    nonfrugalAllocationRule_not_frugal, w1_isSigmaBased,
    nonfrugalVCGSetup_cheating_trueUtility_gt_bundled⟩

end FrugalityNecessityExample

end CombinatorialAuction

/-! ### VCG report redundancy witness -/

namespace RedundantReportVCGExample

/-- Two players are enough to show report-language redundancy. -/
abbrev Player := Fin 2

/-- The first bit is payoff-relevant; the second bit is a redundant report
label. -/
abbrev Report := Bool × Bool

/-- A one-outcome VCG environment.  The allocation is fixed, but reported values
can still enter VCG utilities through the Clarke-style surplus expression. -/
abbrev Outcome := Unit

def value (_i : Player) (r : Report) (_o : Outcome) : ℝ :=
  if r.1 then 1 else 0

def allocation (_report : Player → Report) : Outcome :=
  ()

theorem allocation_efficient :
    ∀ report o, (∑ i : Player, value i (report i) (allocation report)) ≥
      ∑ i : Player, value i (report i) o := by
  intro report o
  cases o
  exact le_rfl

def zeroH (_i : Player) (_report : Player → Report) : ℝ :=
  0

theorem zeroH_independent :
    ∀ i, IndependentOfCoordinate i (zeroH i) := by
  intro i report t
  rfl

/-- A VCG setup with a redundant report bit. -/
noncomputable def setup : VCGSetup Player where
  Θ := fun _ => Report
  Outcome := Outcome
  val := value
  alloc := allocation
  alloc_efficient := allocation_efficient
  h := zeroH
  h_indep := zeroH_independent

/-- Every report is conforming; the conformance bonus is therefore identically
zero. -/
def allReportsConform (_i : Player) (_a : setup.toInformationalGame.Act _i) :
    Prop :=
  True

/-- Flip only the redundant report bit. -/
def flipSecondStrategy : setup.toInformationalGame.StrategyProfile :=
  fun _ r => (r.1, !r.2)

theorem flipSecondStrategy_ne_truthful :
    flipSecondStrategy ≠ setup.truthfulStrategy := by
  intro h
  have h0 := congrFun (congrFun h 0) (false, false)
  have hsecond := congrArg Prod.snd h0
  simp [flipSecondStrategy, VCGSetup.truthfulStrategy] at hsecond

theorem conformanceBonus_zero (B : ℝ)
    (a : setup.toInformationalGame.ActionProfile) (i : Player) :
    setup.toInformationalGame.conformanceBonusTransfer allReportsConform B a i = 0 := by
  classical
  rw [InformationalGame.conformanceBonusTransfer]
  apply if_neg
  rintro ⟨_, j, _, hj⟩
  exact hj trivial

theorem subsidizedUtility_update_eq (B : ℝ)
    (θ : setup.toInformationalGame.SignalProfile)
    (a : setup.toInformationalGame.ActionProfile)
    (i : Player) (x y : setup.toInformationalGame.Act i) :
    setup.toInformationalGame.subsidizedUtility
        (setup.toInformationalGame.conformanceBonusTransfer allReportsConform B)
        θ (Function.update a i x) i =
      setup.toInformationalGame.subsidizedUtility
        (setup.toInformationalGame.conformanceBonusTransfer allReportsConform B)
        θ (Function.update a i y) i := by
  rw [InformationalGame.subsidizedUtility, InformationalGame.subsidizedUtility]
  rw [conformanceBonus_zero, conformanceBonus_zero]
  simp only [add_zero]
  change setup.trueUtility i (θ i) (Function.update a i x) =
    setup.trueUtility i (θ i) (Function.update a i y)
  dsimp [setup, VCGSetup.trueUtility, VCGSetup.vcgPayment, allocation, zeroH, value]
  fin_cases i
  · simp
  · simp

theorem any_strategy_undominated (B : ℝ) (i : Player)
    (s : setup.toInformationalGame.Strategy i) :
    setup.toInformationalGame.IsUndominatedWithTransfer
      (setup.toInformationalGame.conformanceBonusTransfer allReportsConform B) i s := by
  intro c hc
  obtain ⟨_, θ, a, hstrict⟩ := hc
  have heq := subsidizedUtility_update_eq B θ a i (c (θ i)) (s (θ i))
  rw [heq] at hstrict
  exact lt_irrefl _ hstrict

theorem flipSecondStrategy_mem_undominated (B : ℝ) :
    flipSecondStrategy ∈
      setup.toInformationalGame.undominatedStrategyProfilesWithTransfer
        (setup.toInformationalGame.conformanceBonusTransfer allReportsConform B) := by
  intro i
  exact any_strategy_undominated B i (flipSecondStrategy i)

/-- A concrete VCG setup with a distinct undominated strategy profile equivalent
to truthful reporting.  This refutes any unconditional singleton reading of the
VCG conformance-bonus theorem in report languages with redundant reports. -/
theorem undominatedStrategyProfiles_ne_singleton_truthful (B : ℝ) :
    setup.toInformationalGame.undominatedStrategyProfilesWithTransfer
        (setup.toInformationalGame.conformanceBonusTransfer allReportsConform B) ≠
      ({setup.truthfulStrategy} : Set setup.toInformationalGame.StrategyProfile) := by
  intro hsingle
  have hmem := flipSecondStrategy_mem_undominated B
  rw [hsingle] at hmem
  exact flipSecondStrategy_ne_truthful (Set.mem_singleton_iff.mp hmem)

theorem flipSecond_equivalent_truthful (B : ℝ) (i : Player) :
    setup.toInformationalGame.StrategyEquivalentWithTransfer
      (setup.toInformationalGame.conformanceBonusTransfer allReportsConform B)
      i (flipSecondStrategy i) (setup.truthfulStrategy i) := by
  intro θ a
  exact subsidizedUtility_update_eq B θ a i
    (flipSecondStrategy i (θ i)) (setup.truthfulStrategy i (θ i))

/-- The transfer class consisting of conformance-bonus transfers for this
redundant report language. -/
def conformanceBonusTransferClass :
    Set setup.toInformationalGame.ActionTransfer :=
  {V | ∃ B : ℝ,
    V = setup.toInformationalGame.conformanceBonusTransfer allReportsConform B}

/-- The redundant-bit profile is transfer-class equivalent to truthful
reporting for every conformance-bonus transfer in the class. -/
theorem flipSecond_transferClassEquivalent_truthful :
    setup.toInformationalGame.TransferClassStrategyProfileEquivalent
      conformanceBonusTransferClass flipSecondStrategy setup.truthfulStrategy := by
  intro i V hV
  rcases hV with ⟨B, rfl⟩
  exact flipSecond_equivalent_truthful B i

/-- The generic transfer-class saturation theorem re-derives the redundant
report obstruction: no conformance-bonus transfer from this class can
signal-blind implement truthful reporting as a singleton. -/
theorem not_signalBlindImplementation_singleton_truthful_of_conformanceBonusClass
    {V : setup.toInformationalGame.ActionTransfer}
    (hV : V ∈ conformanceBonusTransferClass) :
    ¬ setup.toInformationalGame.IsSignalBlindImplementation V
      ({setup.truthfulStrategy} : Set setup.toInformationalGame.StrategyProfile) := by
  intro h
  have hflip :
      flipSecondStrategy = setup.truthfulStrategy :=
    h.eq_of_transferClassStrategyProfileEquivalent_singleton hV
      flipSecond_transferClassEquivalent_truthful
  exact flipSecondStrategy_ne_truthful hflip

end RedundantReportVCGExample

end GameTheory
