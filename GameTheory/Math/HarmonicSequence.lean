/-
# Harmonic-energy sequence estimates

Two real-sequence lemmas used by fictitious-play convergence.  They are
independent of games and finite probability: summable harmonic energy forces
arbitrarily small late values, and an `O(1/n)` adjacent-variation bound upgrades
that recurrence to convergence to zero.
-/

import Mathlib.Analysis.PSeries

namespace GameTheory.Math

open Filter

/-- If `∑ (x n)/(n+2)` converges absolutely, then `x n` is arbitrarily small
along arbitrarily late indices. -/
theorem frequently_lt_of_summable_one_div_mul
    {x : ℕ → ℝ}
    (hs : Summable (fun n : ℕ => (1 / ((n : ℝ) + 2)) * x n))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n in atTop, x n < ε := by
  let weight : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  let weighted : ℕ → ℝ := fun n => weight n * x n
  have hsWeighted : Summable weighted := by
    simpa [weighted, weight, mul_comm] using hs
  by_contra hfrequent
  rw [not_frequently] at hfrequent
  have heventually : ∀ᶠ n in atTop, ε ≤ x n := by
    filter_upwards [hfrequent] with n hn
    exact le_of_not_gt hn
  have hsScaledWeight : Summable (fun n : ℕ => ε * weight n) := by
    refine hsWeighted.of_norm_bounded_eventually_nat ?_
    filter_upwards [heventually] with n hn
    have hweight : 0 ≤ weight n := by
      dsimp [weight]
      positivity
    have hle : ε * weight n ≤ weighted n := by
      calc
        ε * weight n = weight n * ε := by ring
        _ ≤ weight n * x n := mul_le_mul_of_nonneg_left hn hweight
        _ = weighted n := by rfl
    rw [Real.norm_of_nonneg (mul_nonneg hε.le hweight)]
    exact hle
  have hsWeight : Summable weight := by
    have hscaled : Summable (fun n : ℕ => ε⁻¹ * (ε * weight n)) :=
      hsScaledWeight.mul_left ε⁻¹
    refine hscaled.congr ?_
    intro n
    calc
      ε⁻¹ * (ε * weight n) = (ε⁻¹ * ε) * weight n := by ring
      _ = 1 * weight n := by rw [inv_mul_cancel₀ hε.ne']
      _ = weight n := by ring
  have hsTail : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
    simpa [weight] using hsWeight
  have hsHarmonic : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    have hsShift : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
      simpa [Nat.cast_add] using hsTail
    exact (summable_nat_add_iff 2).mp hsShift
  exact Real.not_summable_one_div_natCast hsHarmonic

/-- A Tauberian estimate for nonnegative sequences with harmonic energy: if
`∑ x n/(n+2)` converges and adjacent terms change by `O(1/(n+2))`, then
`x n → 0`. -/
theorem tendsto_zero_of_summable_one_div_mul_of_succ_abs_sub_le
    {x : ℕ → ℝ}
    (hxNonneg : ∀ n, 0 ≤ x n)
    (hs : Summable (fun n : ℕ => (1 / ((n : ℝ) + 2)) * x n))
    {K : ℝ} (hKNonneg : 0 ≤ K)
    (hslow : ∀ n : ℕ, |x (n + 1) - x n| ≤ K / ((n : ℝ) + 2)) :
    Tendsto x atTop (nhds 0) := by
  let weighted : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 2)) * x n
  have hsWeighted : Summable weighted := by simpa [weighted] using hs
  have hweightedNonneg : ∀ n, 0 ≤ weighted n := by
    intro n
    dsimp [weighted]
    exact mul_nonneg (by positivity) (hxNonneg n)
  rw [tendsto_order]
  constructor
  · intro lower hlower
    filter_upwards with n
    exact lt_of_lt_of_le hlower (hxNonneg n)
  · intro ε hε
    have hdenBase : 0 < ε / (4 * (K + 1)) := by positivity
    obtain ⟨q0, hq0⟩ := exists_nat_one_div_lt hdenBase
    let q : ℕ := q0 + 1
    have hqNat : 0 < q := by dsimp [q]; omega
    have hq : 0 < (q : ℝ) := by exact_mod_cast hqNat
    have hKp : 0 < K + 1 := by linarith
    have hqSmall : K / (q : ℝ) < ε / 4 := by
      have hq0' : 1 / (q : ℝ) < ε / (4 * (K + 1)) := by
        simpa [q, Nat.cast_add, add_comm] using hq0
      calc
        K / (q : ℝ) ≤ (K + 1) / (q : ℝ) := by
          exact div_le_div_of_nonneg_right (by linarith) hq.le
        _ = (K + 1) * (1 / (q : ℝ)) := by ring
        _ < (K + 1) * (ε / (4 * (K + 1))) := by
          exact mul_lt_mul_of_pos_left hq0' hKp
        _ = ε / 4 := by
          field_simp [hKp.ne']
    let δ : ℝ := ε / (16 * (q : ℝ))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have htailTendsto :
        Tendsto (fun n : ℕ => ∑' k : ℕ, weighted (k + n)) atTop (nhds 0) :=
      tendsto_sum_nat_add weighted
    have htailEvent :
        ∀ᶠ n in atTop, (∑' k : ℕ, weighted (k + n)) < δ :=
      htailTendsto.eventually (eventually_lt_nhds hδ)
    have hlargeEvent : ∀ᶠ n in atTop, 2 * q ≤ n + 2 :=
      eventually_atTop.2 ⟨2 * q, fun n hn => by omega⟩
    filter_upwards [htailEvent, hlargeEvent] with n htail hlarge
    by_contra hnlt
    have hxn : ε ≤ x n := le_of_not_gt hnlt
    let N : ℕ := n + 2
    let L : ℕ := N / q
    have hNnat : 0 < N := by dsimp [N]; omega
    have hN : 0 < (N : ℝ) := by exact_mod_cast hNnat
    have hlargeN : 2 * q ≤ N := by simpa [N] using hlarge
    have hLUpper : ((L : ℕ) : ℝ) ≤ (N : ℝ) / (q : ℝ) := by
      dsimp [L]
      have hmulNat : N / q * q ≤ N := Nat.div_mul_le_self N q
      have hmulReal : ((N / q : ℕ) : ℝ) * (q : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hmulNat
      rw [le_div_iff₀ hq]
      simpa [mul_comm] using hmulReal
    have hLLower : (N : ℝ) / (2 * (q : ℝ)) ≤ ((L : ℕ) : ℝ) := by
      dsimp [L]
      have hprod : N - q ≤ N / q * q := by
        have hdiv : q * (N / q) + N % q = N := Nat.div_add_mod N q
        rw [Nat.mul_comm] at hdiv
        have hmod : N % q < q := Nat.mod_lt N hqNat
        omega
      have hhalf : N ≤ 2 * (N - q) := by omega
      have hmulNat : N ≤ 2 * (N / q * q) := by omega
      have hmulReal : (N : ℝ) ≤ 2 * (((N / q : ℕ) : ℝ) * (q : ℝ)) := by
        exact_mod_cast hmulNat
      have hden : 0 < (2 : ℝ) * (q : ℝ) := by positivity
      calc
        (N : ℝ) / (2 * (q : ℝ)) ≤
            (2 * (((N / q : ℕ) : ℝ) * (q : ℝ))) /
              (2 * (q : ℝ)) := by
          exact div_le_div_of_nonneg_right hmulReal hden.le
        _ = ((N / q : ℕ) : ℝ) := by
          field_simp [hq.ne']
    have hxBlock : ∀ j : ℕ, j ≤ L → x (n + j) ≥ ε / 2 := by
      intro j hjL
      have hdrop : x n - ((j : ℝ) * (K / (N : ℝ))) ≤ x (n + j) := by
        induction j with
        | zero => simp
        | succ j ih =>
            have hjL' : j ≤ L := le_trans (Nat.le_succ j) hjL
            have hprevious := ih hjL'
            have hstepAbs := hslow (n + j)
            have hstepLower :
                x (n + j) - K / ((n + j : ℝ) + 2) ≤
                  x (n + (j + 1)) := by
              have hlower := (abs_le.mp hstepAbs).1
              rw [show n + (j + 1) = n + j + 1 by omega]
              norm_num [Nat.cast_add] at hlower ⊢
              linarith
            have hdenLe : K / ((n + j : ℝ) + 2) ≤ K / (N : ℝ) := by
              have hden : (N : ℝ) ≤ (n + j : ℝ) + 2 := by
                dsimp [N]
                norm_num
              exact div_le_div_of_nonneg_left hKNonneg hN hden
            have hnext :
                x n - (((j + 1 : ℕ) : ℝ) * (K / (N : ℝ))) ≤
                  x (n + (j + 1)) := by
              calc
                x n - (((j + 1 : ℕ) : ℝ) * (K / (N : ℝ))) =
                    (x n - ((j : ℝ) * (K / (N : ℝ)))) - K / (N : ℝ) := by
                  norm_num
                  ring
                _ ≤ x (n + j) - K / (N : ℝ) := by linarith
                _ ≤ x (n + j) - K / ((n + j : ℝ) + 2) := by linarith
                _ ≤ x (n + (j + 1)) := hstepLower
            simpa using hnext
      have hjBound : (j : ℝ) * (K / (N : ℝ)) ≤ K / (q : ℝ) := by
        have hjReal : (j : ℝ) ≤ (L : ℝ) := by exact_mod_cast hjL
        have hLj : (j : ℝ) ≤ (N : ℝ) / (q : ℝ) := hjReal.trans hLUpper
        have hKN : 0 ≤ K / (N : ℝ) := div_nonneg hKNonneg hN.le
        calc
          (j : ℝ) * (K / (N : ℝ)) ≤
              ((N : ℝ) / (q : ℝ)) * (K / (N : ℝ)) :=
            mul_le_mul_of_nonneg_right hLj hKN
          _ = K / (q : ℝ) := by
            field_simp [hN.ne', hq.ne']
      linarith
    have hblockPoint :
        ∀ k ∈ Finset.range L, ε / (4 * (N : ℝ)) ≤ weighted (n + k) := by
      intro k hk
      have hkL : k ≤ L := le_of_lt (Finset.mem_range.mp hk)
      have hxk : ε / 2 ≤ x (n + k) := hxBlock k hkL
      have hweight :
          1 / (((n + k : ℕ) : ℝ) + 2) ≥ 1 / (2 * (N : ℝ)) := by
        have hkN : k ≤ N := hkL.trans (Nat.div_le_self N q)
        have hden : ((n + k : ℕ) : ℝ) + 2 ≤ 2 * (N : ℝ) := by
          dsimp [N]
          exact_mod_cast (by omega : n + k + 2 ≤ 2 * (n + 2))
        have hdenPos : 0 < ((n + k : ℕ) : ℝ) + 2 := by positivity
        exact one_div_le_one_div_of_le hdenPos hden
      dsimp [weighted]
      calc
        ε / (4 * (N : ℝ)) = (1 / (2 * (N : ℝ))) * (ε / 2) := by ring
        _ ≤ (1 / (((n + k : ℕ) : ℝ) + 2)) * x (n + k) := by
          exact mul_le_mul hweight hxk (by positivity) (by positivity)
    have hblockLower :
        ε / (8 * (q : ℝ)) ≤ ∑ k ∈ Finset.range L, weighted (n + k) := by
      have hconst : 0 ≤ ε / (4 * (N : ℝ)) := by positivity
      calc
        ε / (8 * (q : ℝ)) =
            ((N : ℝ) / (2 * (q : ℝ))) * (ε / (4 * (N : ℝ))) := by
          field_simp [hN.ne', hq.ne']
          ring
        _ ≤ (L : ℝ) * (ε / (4 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hLLower hconst
        _ = ∑ k ∈ Finset.range L, ε / (4 * (N : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ k ∈ Finset.range L, weighted (n + k) :=
          Finset.sum_le_sum hblockPoint
    have htail' : (∑' k : ℕ, weighted (n + k)) < δ := by
      simpa [Nat.add_comm] using htail
    have htailSummable : Summable (fun k : ℕ => weighted (n + k)) := by
      simpa [Function.comp_def] using
        hsWeighted.comp_injective (i := fun k => n + k) (add_right_injective n)
    have hfiniteTail :
        ∑ k ∈ Finset.range L, weighted (n + k) ≤
          ∑' k : ℕ, weighted (n + k) :=
      htailSummable.sum_le_tsum (Finset.range L)
        (fun k _ => hweightedNonneg (n + k))
    have hcontr : ε / (8 * (q : ℝ)) < ε / (16 * (q : ℝ)) :=
      lt_of_le_of_lt (hblockLower.trans hfiniteTail) htail'
    have hrewrite :
        ε / (8 * (q : ℝ)) = 2 * (ε / (16 * (q : ℝ))) := by
      field_simp [hq.ne']
      ring
    rw [hrewrite] at hcontr
    have hpos : 0 < ε / (16 * (q : ℝ)) := by positivity
    nlinarith

end GameTheory.Math
