import Math.GateGTermination
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

set_option autoImplicit false
set_option linter.unusedFintypeInType false

noncomputable section

open Filter Polynomial
open UniqueFactorizationMonoid

namespace Math
namespace GateGFactorCoverageScratch

variable {K : Type*} [Field K]

local instance chosenNormalizationMonoid :
    NormalizationMonoid (Polynomial (Polynomial K)) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid

/-- A fixed finite multiset of irreducible factors, using the canonical
choice of normalization supplied noncomputably by unique factorization. -/
noncomputable def irreducibleFactors
    (Q : Polynomial (Polynomial K)) :
    Multiset (Polynomial (Polynomial K)) :=
  normalizedFactors Q

/-- Every zero of a nonzero primitive bivariate polynomial lies on one of
its finitely many normalized irreducible factors; primitivity ensures that
such a factor has positive degree in the outer variable. -/
theorem exists_positiveDegree_irreducibleFactor_isRoot
    (Q : Polynomial (Polynomial K))
    (hQ : Q ≠ 0)
    (hprimitive : Q.IsPrimitive)
    (x y : K)
    (hroot :
      GateGTerminationScratch.bivEvalAt Q x y = 0) :
    ∃ q : Polynomial (Polynomial K),
      q ∈ irreducibleFactors Q ∧
      Irreducible q ∧
      0 < q.natDegree ∧
      q ∣ Q ∧
      GateGTerminationScratch.bivEvalAt q x y = 0 := by
  classical
  let e : Polynomial (Polynomial K) →+* K :=
    Polynomial.eval₂RingHom (Polynomial.evalRingHom x) y
  obtain ⟨u, hu⟩ := prod_normalizedFactors hQ
  have heu : IsUnit (e (u : Polynomial (Polynomial K))) :=
    u.isUnit.map e
  have heprod :
      e (normalizedFactors Q).prod = 0 := by
    have heq := congrArg e hu
    have heQ : e Q = 0 := hroot
    rw [map_mul, heQ] at heq
    exact (mul_eq_zero.mp heq).resolve_right heu.ne_zero
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at heprod
  obtain ⟨q, hqmem, hqzero⟩ :=
    Multiset.mem_map.mp heprod
  have hqmem' : q ∈ irreducibleFactors Q := by
    simpa [irreducibleFactors] using hqmem
  have hqirr : Irreducible q :=
    irreducible_of_normalized_factor q hqmem
  have hqdvd : q ∣ Q :=
    dvd_of_mem_normalizedFactors hqmem
  have hqdegree : 0 < q.natDegree := by
    by_contra hnot
    have hdegree : q.natDegree ≤ 0 := Nat.le_zero.mpr
      (Nat.eq_zero_of_not_pos hnot)
    have hqC : q = Polynomial.C (q.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero hdegree
    have hCdiv : Polynomial.C (q.coeff 0) ∣ Q := by
      rw [hqC] at hqdvd
      exact hqdvd
    have hcoeffUnit : IsUnit (q.coeff 0) :=
      (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprimitive)
        (q.coeff 0) hCdiv
    have hqUnit : IsUnit q := by
      rw [hqC]
      exact hcoeffUnit.map Polynomial.C
    exact hqirr.not_isUnit hqUnit
  exact
    ⟨q, hqmem', hqirr, hqdegree, hqdvd,
      by simpa [e, GateGTerminationScratch.bivEvalAt] using hqzero⟩

/-- Along an infinite sequence of roots, one fixed positive-degree
irreducible factor recurs frequently. -/
theorem exists_positiveDegree_irreducibleFactor_frequently_isRoot
    (Q : Polynomial (Polynomial K))
    (hQ : Q ≠ 0)
    (hprimitive : Q.IsPrimitive)
    (x y : ℕ → K)
    (hroot :
      ∀ n,
        GateGTerminationScratch.bivEvalAt Q (x n) (y n) = 0) :
    ∃ q : Polynomial (Polynomial K),
      q ∈ irreducibleFactors Q ∧
      Irreducible q ∧
      0 < q.natDegree ∧
      q ∣ Q ∧
      ∃ᶠ n in atTop,
        GateGTerminationScratch.bivEvalAt q (x n) (y n) = 0 := by
  classical
  choose q hqmem hqirr hqdegree hqdvd hqroot using
    fun n =>
      exists_positiveDegree_irreducibleFactor_isRoot
        Q hQ hprimitive (x n) (y n) (hroot n)
  let F : Finset (Polynomial (Polynomial K)) :=
    (irreducibleFactors Q).toFinset
  let selected : ℕ → ↥F :=
    fun n => ⟨q n, by simpa [F] using hqmem n⟩
  have hsome :
      ∃ᶠ n in atTop, ∃ a : ↥F, selected n = a :=
    Filter.Frequently.of_forall fun n => ⟨selected n, rfl⟩
  rw [Filter.frequently_exists] at hsome
  obtain ⟨a, ha⟩ := hsome
  obtain ⟨n₀, hn₀⟩ := ha.exists
  have hqeq₀ : q n₀ = a.1 :=
    congrArg Subtype.val hn₀
  refine ⟨a.1, ?_, ?_, ?_, ?_, ?_⟩
  · have haF : a.1 ∈ F := a.2
    change a.1 ∈ (irreducibleFactors Q).toFinset at haF
    simpa only [Multiset.mem_toFinset] using haF
  · simpa [hqeq₀] using hqirr n₀
  · simpa [hqeq₀] using hqdegree n₀
  · simpa [hqeq₀] using hqdvd n₀
  · apply ha.mono
    intro n hn
    have hqeq : q n = a.1 :=
      congrArg Subtype.val hn
    simpa [hqeq] using hqroot n

/-- Subsequence form: the recurring factor can be made to vanish at every
term while preserving any pre-existing filter limit of the sampled pairs. -/
theorem exists_positiveDegree_irreducibleFactor_subsequence_isRoot
    (Q : Polynomial (Polynomial K))
    (hQ : Q ≠ 0)
    (hprimitive : Q.IsPrimitive)
    (x y : ℕ → K)
    {l : Filter (K × K)}
    (hlim : Tendsto (fun n => (x n, y n)) atTop l)
    (hroot :
      ∀ n,
        GateGTerminationScratch.bivEvalAt Q (x n) (y n) = 0) :
    ∃ (q : Polynomial (Polynomial K)) (ns : ℕ → ℕ),
      q ∈ irreducibleFactors Q ∧
      Irreducible q ∧
      0 < q.natDegree ∧
      q ∣ Q ∧
      Tendsto (fun n => (x (ns n), y (ns n))) atTop l ∧
      ∀ n,
        GateGTerminationScratch.bivEvalAt
          q (x (ns n)) (y (ns n)) = 0 := by
  obtain ⟨q, hqmem, hqirr, hqdegree, hqdvd, hqfrequent⟩ :=
    exists_positiveDegree_irreducibleFactor_frequently_isRoot
      Q hQ hprimitive x y hroot
  have hqfrequent' :
      ∃ᶠ n in atTop,
        (fun w : K × K =>
          GateGTerminationScratch.bivEvalAt q w.1 w.2 = 0)
          (x n, y n) := by
    simpa using hqfrequent
  obtain ⟨ns, hlimsub, hqroot⟩ :=
    Filter.subseq_forall_of_frequently
      (x := fun n => (x n, y n))
      (p := fun w : K × K =>
        GateGTerminationScratch.bivEvalAt q w.1 w.2 = 0)
      (l := l) hlim hqfrequent'
  exact
    ⟨q, ns, hqmem, hqirr, hqdegree, hqdvd, hlimsub,
      by simpa using hqroot⟩

/-- Simultaneous finite-factor synchronization for finitely many coordinate
relations.  One tuple of positive-degree irreducible factors vanishes
frequently across all coordinates. -/
theorem exists_irreducibleFactorTuple_frequently_isRoot
    {σ : Type*} [Fintype σ]
    (Q : σ → Polynomial (Polynomial K))
    (hQ : ∀ j, Q j ≠ 0)
    (hprimitive : ∀ j, (Q j).IsPrimitive)
    (x : ℕ → K)
    (y : ℕ → σ → K)
    (hroot :
      ∀ n j,
        GateGTerminationScratch.bivEvalAt
          (Q j) (x n) (y n j) = 0) :
    ∃ q : σ → Polynomial (Polynomial K),
      (∀ j,
        q j ∈ irreducibleFactors (Q j) ∧
        Irreducible (q j) ∧
        0 < (q j).natDegree ∧
        q j ∣ Q j) ∧
      ∃ᶠ n in atTop,
        ∀ j,
          GateGTerminationScratch.bivEvalAt
            (q j) (x n) (y n j) = 0 := by
  classical
  choose q hqmem hqirr hqdegree hqdvd hqroot using
    fun n j =>
      exists_positiveDegree_irreducibleFactor_isRoot
        (Q j) (hQ j) (hprimitive j)
        (x n) (y n j) (hroot n j)
  let F : σ → Finset (Polynomial (Polynomial K)) :=
    fun j => (irreducibleFactors (Q j)).toFinset
  let selected : ℕ → (∀ j, ↥(F j)) :=
    fun n j => ⟨q n j, by simpa [F] using hqmem n j⟩
  have hsome :
      ∃ᶠ n in atTop,
        ∃ a : ∀ j, ↥(F j), selected n = a :=
    Filter.Frequently.of_forall fun n => ⟨selected n, rfl⟩
  rw [Filter.frequently_exists] at hsome
  obtain ⟨a, ha⟩ := hsome
  obtain ⟨n₀, hn₀⟩ := ha.exists
  have hqeq₀ : ∀ j, q n₀ j = (a j).1 := by
    intro j
    exact congrFun (congrArg (fun b => fun j => (b j).1) hn₀) j
  let factor : σ → Polynomial (Polynomial K) :=
    fun j => (a j).1
  refine ⟨factor, ?_, ?_⟩
  · intro j
    have hajF : (a j).1 ∈ F j := (a j).2
    have hajmem :
        factor j ∈ irreducibleFactors (Q j) := by
      change (a j).1 ∈ irreducibleFactors (Q j)
      change (a j).1 ∈
        (irreducibleFactors (Q j)).toFinset at hajF
      simpa only [Multiset.mem_toFinset] using hajF
    refine ⟨hajmem, ?_, ?_, ?_⟩
    · simpa [factor, hqeq₀ j] using hqirr n₀ j
    · simpa [factor, hqeq₀ j] using hqdegree n₀ j
    · simpa [factor, hqeq₀ j] using hqdvd n₀ j
  · apply ha.mono
    intro n hn j
    have hqeq : q n j = factor j := by
      change q n j = (a j).1
      exact congrFun (congrArg (fun b => fun j => (b j).1) hn) j
    simpa [hqeq] using hqroot n j

/-- Coupled subsequence version of finite-factor synchronization. -/
theorem exists_irreducibleFactorTuple_subsequence_isRoot
    {σ : Type*} [Fintype σ]
    (Q : σ → Polynomial (Polynomial K))
    (hQ : ∀ j, Q j ≠ 0)
    (hprimitive : ∀ j, (Q j).IsPrimitive)
    (x : ℕ → K)
    (y : ℕ → σ → K)
    {l : Filter (K × (σ → K))}
    (hlim : Tendsto (fun n => (x n, y n)) atTop l)
    (hroot :
      ∀ n j,
        GateGTerminationScratch.bivEvalAt
          (Q j) (x n) (y n j) = 0) :
    ∃ (q : σ → Polynomial (Polynomial K)) (ns : ℕ → ℕ),
      (∀ j,
        q j ∈ irreducibleFactors (Q j) ∧
        Irreducible (q j) ∧
        0 < (q j).natDegree ∧
        q j ∣ Q j) ∧
      Tendsto (fun n => (x (ns n), y (ns n))) atTop l ∧
      ∀ n j,
        GateGTerminationScratch.bivEvalAt
          (q j) (x (ns n)) (y (ns n) j) = 0 := by
  obtain ⟨q, hq, hqfrequent⟩ :=
    exists_irreducibleFactorTuple_frequently_isRoot
      Q hQ hprimitive x y hroot
  have hqfrequent' :
      ∃ᶠ n in atTop,
        (fun w : K × (σ → K) =>
          ∀ j,
            GateGTerminationScratch.bivEvalAt
              (q j) w.1 (w.2 j) = 0)
          (x n, y n) := by
    simpa using hqfrequent
  obtain ⟨ns, hlimsub, hqroot⟩ :=
    Filter.subseq_forall_of_frequently
      (x := fun n => (x n, y n))
      (p := fun w : K × (σ → K) =>
        ∀ j,
          GateGTerminationScratch.bivEvalAt
            (q j) w.1 (w.2 j) = 0)
      (l := l) hlim hqfrequent'
  exact ⟨q, ns, hq, hlimsub, by simpa using hqroot⟩

end GateGFactorCoverageScratch
end Math
