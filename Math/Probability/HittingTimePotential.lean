/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.MeanErgodic

/-!
# Finite-state hitting-time potentials

For a finite Markov kernel and a closed core, a uniform positive probability
of reaching the core within a fixed number of steps makes the killed Poisson
operator invertible.  Its inverse applied to the transient-state indicator is
a nonnegative potential satisfying the exact one-step Poisson equation.

The theorem is deliberately stated with an explicit finite-step survival
bound.  It does not assume an already-developed infinite-horizon hitting-time
random variable.
-/

namespace Math.Probability

open Math.ProbabilityMassFunction

noncomputable section

variable {S : Type*}

/-- The indicator of the complement of a proposed closed core. -/
noncomputable def transientCharge (core : Set S) (s : S) : ℝ := by
  classical
  exact if s ∈ core then 0 else 1

@[simp] theorem transientCharge_of_mem {core : Set S} {s : S}
    (hs : s ∈ core) :
    transientCharge core s = 0 := by
  simp [transientCharge, hs]

@[simp] theorem transientCharge_of_not_mem {core : Set S} {s : S}
    (hs : s ∉ core) :
    transientCharge core s = 1 := by
  simp [transientCharge, hs]

theorem transientCharge_nonneg (core : Set S) (s : S) :
    0 ≤ transientCharge core s := by
  by_cases hs : s ∈ core <;> simp [transientCharge, hs]

theorem transientCharge_le_one (core : Set S) (s : S) :
    transientCharge core s ≤ 1 := by
  by_cases hs : s ∈ core <;> simp [transientCharge, hs]

/-- A set is closed for a PMF kernel when every one-step successor in the
support of the kernel remains in the set. -/
def IsClosedCore (kernel : S → PMF S) (core : Set S) : Prop :=
  ∀ ⦃s⦄, s ∈ core → ∀ ⦃u⦄, u ∈ (kernel s).support → u ∈ core

/-- Functions that vanish on the closed core. -/
def coreVanishingSubmodule (core : Set S) : Submodule ℝ (S → ℝ) where
  carrier := {f | ∀ ⦃s⦄, s ∈ core → f s = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg s hs
    simp [hf hs, hg hs]
  smul_mem' := by
    intro c f hf s hs
    simp [hf hs]

@[simp] theorem mem_coreVanishingSubmodule_iff
    {core : Set S} {f : S → ℝ} :
    f ∈ coreVanishingSubmodule core ↔
      ∀ ⦃s⦄, s ∈ core → f s = 0 :=
  Iff.rfl

theorem expect_eq_zero_of_mem_coreVanishing
    {kernel : S → PMF S} {core : Set S}
    (hclosed : IsClosedCore kernel core)
    {f : S → ℝ} (hf : f ∈ coreVanishingSubmodule core)
    {s : S} (hs : s ∈ core) :
    expect (kernel s) f = 0 := by
  calc
    expect (kernel s) f = expect (kernel s) (fun _ => 0) := by
      apply expect_congr_on_support
      intro u hu
      exact hf (hclosed hs hu)
    _ = 0 := expect_const _ 0

/-- The Markov operator preserves functions vanishing on a closed core. -/
theorem markovOperator_maps_coreVanishing
    [Fintype S]
    {kernel : S → PMF S} {core : Set S}
    (hclosed : IsClosedCore kernel core) :
    Set.MapsTo (Math.MeanErgodic.markovOperator kernel)
      (coreVanishingSubmodule core) (coreVanishingSubmodule core) := by
  intro f hf s hs
  exact expect_eq_zero_of_mem_coreVanishing hclosed hf hs

/-- The Markov operator restricted to functions vanishing on the core. -/
def killedMarkovOperator
    [Fintype S]
    (kernel : S → PMF S) (core : Set S)
    (hclosed : IsClosedCore kernel core) :
    coreVanishingSubmodule core →ₗ[ℝ] coreVanishingSubmodule core :=
  LinearMap.restrict (Math.MeanErgodic.markovOperator kernel)
    (markovOperator_maps_coreVanishing hclosed)

@[simp] theorem killedMarkovOperator_apply
    [Fintype S]
    (kernel : S → PMF S) (core : Set S)
    (hclosed : IsClosedCore kernel core)
    (f : coreVanishingSubmodule core) (s : S) :
    (killedMarkovOperator kernel core hclosed f : S → ℝ) s =
      expect (kernel s) f := by
  rfl

/-- Uniform `m`-step reachability of the core, expressed as an upper bound
on the probability of still being outside the core after `m` steps. -/
def HasUniformCoreReach
    (kernel : S → PMF S) (core : Set S) (m : ℕ) (δ : ℝ) : Prop :=
  ∀ s,
    expect (Math.PMFIter.iter kernel m s) (transientCharge core) ≤ 1 - δ

/-- Absolute expectation is bounded by the expectation of the absolute
value on a finite sample space. -/
theorem abs_expect_le_expect_abs [Finite S] (d : PMF S) (f : S → ℝ) :
    |expect d f| ≤ expect d (fun s => |f s|) := by
  letI : Fintype S := Fintype.ofFinite S
  rw [expect_eq_sum, expect_eq_sum]
  calc
    |∑ s : S, (d s).toReal * f s| ≤
        ∑ s : S, |(d s).toReal * f s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s : S, (d s).toReal * |f s| := by
      apply Finset.sum_congr rfl
      intro s _
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]

/-- A function vanishing on the core is bounded under expectation by its
sup norm times the probability of remaining outside the core. -/
theorem abs_expect_le_norm_mul_transientProbability
    [Fintype S]
    (d : PMF S) (core : Set S) (f : S → ℝ)
    (hf : f ∈ coreVanishingSubmodule core) :
    |expect d f| ≤
      ‖f‖ * expect d (transientCharge core) := by
  calc
    |expect d f| ≤ expect d (fun s => |f s|) :=
      abs_expect_le_expect_abs d f
    _ ≤ expect d (fun s => ‖f‖ * transientCharge core s) := by
      apply expect_mono
      intro s
      by_cases hs : s ∈ core
      · simp [transientCharge, hs, hf hs]
      · simpa [transientCharge, hs, Real.norm_eq_abs] using
          norm_le_pi_norm f s
    _ = ‖f‖ * expect d (transientCharge core) :=
      expect_const_mul d ‖f‖ (transientCharge core)

/-- A fixed point of the Markov operator equals the expected value of itself
under every finite iterate of the kernel. -/
theorem expect_iter_eq_of_markovOperator_fixed
    [Fintype S]
    {kernel : S → PMF S} {f : S → ℝ}
    (hfixed : Math.MeanErgodic.markovOperator kernel f = f)
    (m : ℕ) (s : S) :
    expect (Math.PMFIter.iter kernel m s) f = f s := by
  rw [← Math.MeanErgodic.markovOperator_pow_apply]
  exact congrFun (Math.MeanErgodic.pow_apply_eq_of_fixed hfixed m) s

/-- The killed Poisson operator `I - P` on functions vanishing on the core. -/
def killedPoissonOperator
    [Fintype S]
    (kernel : S → PMF S) (core : Set S)
    (hclosed : IsClosedCore kernel core) :
    coreVanishingSubmodule core →ₗ[ℝ] coreVanishingSubmodule core :=
  LinearMap.id - killedMarkovOperator kernel core hclosed

/-- The killed operator has no nonzero harmonic function under uniform
finite-step reachability of the core. -/
theorem killedPoissonOperator_injective
    [Fintype S] [Nonempty S]
    {kernel : S → PMF S} {core : Set S}
    (hclosed : IsClosedCore kernel core)
    {m : ℕ} {δ : ℝ}
    (hδpos : 0 < δ) (hδone : δ ≤ 1)
    (hreach : HasUniformCoreReach kernel core m δ) :
    Function.Injective (killedPoissonOperator kernel core hclosed) := by
  intro f g hfg
  have hsub :
      killedPoissonOperator kernel core hclosed (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  let z : coreVanishingSubmodule core := f - g
  have hfixedKilled :
      killedMarkovOperator kernel core hclosed z = z := by
    have hz := hsub
    change z - killedMarkovOperator kernel core hclosed z = 0 at hz
    exact (sub_eq_zero.mp hz).symm
  have hfixed :
      Math.MeanErgodic.markovOperator kernel (z : S → ℝ) = z := by
    ext s
    exact congrFun (congrArg Subtype.val hfixedKilled) s
  have hpoint (s : S) :
      |(z : S → ℝ) s| ≤ ‖(z : S → ℝ)‖ * (1 - δ) := by
    rw [← expect_iter_eq_of_markovOperator_fixed hfixed m s]
    calc
      |expect (Math.PMFIter.iter kernel m s) (z : S → ℝ)| ≤
          ‖(z : S → ℝ)‖ *
            expect (Math.PMFIter.iter kernel m s)
              (transientCharge core) :=
        abs_expect_le_norm_mul_transientProbability
          (Math.PMFIter.iter kernel m s) core z z.property
      _ ≤ ‖(z : S → ℝ)‖ * (1 - δ) :=
        mul_le_mul_of_nonneg_left (hreach s) (norm_nonneg _)
  have hnorm :
      ‖(z : S → ℝ)‖ ≤ ‖(z : S → ℝ)‖ * (1 - δ) := by
    rw [pi_norm_le_iff_of_nonneg]
    · intro s
      simpa [Real.norm_eq_abs] using hpoint s
    · exact mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hδone)
  have hzNorm : ‖(z : S → ℝ)‖ = 0 := by
    nlinarith [norm_nonneg (z : S → ℝ)]
  have hzZero : z = 0 := by
    apply Subtype.ext
    exact norm_eq_zero.mp hzNorm
  exact sub_eq_zero.mp hzZero

/-- The transient charge itself vanishes on the core. -/
theorem transientCharge_mem_coreVanishing (core : Set S) :
    transientCharge core ∈ coreVanishingSubmodule core := by
  intro s hs
  exact transientCharge_of_mem hs

/-- Finite-dimensional Poisson solvability on the killed state space. -/
theorem exists_coreVanishing_poissonPotential
    [Fintype S] [Nonempty S]
    {kernel : S → PMF S} {core : Set S}
    (hclosed : IsClosedCore kernel core)
    {m : ℕ} {δ : ℝ}
    (hδpos : 0 < δ) (hδone : δ ≤ 1)
    (hreach : HasUniformCoreReach kernel core m δ) :
    ∃ h : coreVanishingSubmodule core,
      killedPoissonOperator kernel core hclosed h =
        ⟨transientCharge core, transientCharge_mem_coreVanishing core⟩ := by
  have hinj := killedPoissonOperator_injective
    hclosed hδpos hδone hreach
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  exact hsurj ⟨transientCharge core,
    transientCharge_mem_coreVanishing core⟩

/-- The core-vanishing Poisson potential is unique under the same uniform
finite-step reach hypothesis. -/
theorem poissonPotential_unique_of_uniformCoreReach
    [Finite S] [Nonempty S]
    {kernel : S → PMF S} {core : Set S}
    (hclosed : IsClosedCore kernel core)
    {m : ℕ} {δ : ℝ}
    (hδpos : 0 < δ) (hδone : δ ≤ 1)
    (hreach : HasUniformCoreReach kernel core m δ)
    {f g : S → ℝ}
    (hfcore : f ∈ coreVanishingSubmodule core)
    (hgcore : g ∈ coreVanishingSubmodule core)
    (hf : ∀ s,
      f s - expect (kernel s) f = transientCharge core s)
    (hg : ∀ s,
      g s - expect (kernel s) g = transientCharge core s) :
    f = g := by
  letI : Fintype S := Fintype.ofFinite S
  let f' : coreVanishingSubmodule core := ⟨f, hfcore⟩
  let g' : coreVanishingSubmodule core := ⟨g, hgcore⟩
  have hoperators :
      killedPoissonOperator kernel core hclosed f' =
        killedPoissonOperator kernel core hclosed g' := by
    apply Subtype.ext
    funext s
    change
      f s - expect (kernel s) f =
        g s - expect (kernel s) g
    rw [hf s, hg s]
  have hfg : f' = g' :=
    killedPoissonOperator_injective
      hclosed hδpos hδone hreach hoperators
  exact congrArg Subtype.val hfg

/-- Iterating a one-step Poisson equation gives the finite-horizon
potential decomposition. -/
theorem poissonPotential_eq_sum_expect_add_expect_iter
    [Finite S]
    {kernel : S → PMF S} {potential charge : S → ℝ}
    (hpoisson : ∀ s,
      potential s - expect (kernel s) potential = charge s)
    (m : ℕ) (s : S) :
    potential s =
      (∑ t ∈ Finset.range m,
        expect (Math.PMFIter.iter kernel t s) charge) +
      expect (Math.PMFIter.iter kernel m s) potential := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Math.PMFIter.iter_succ', expect_bind]
      have hinner :
          (fun u =>
              expect (kernel u) potential) =
            fun u => potential u - charge u := by
        funext u
        linarith [hpoisson u]
      rw [hinner, expect_sub]
      have hstep :
          expect (Math.PMFIter.iter kernel m s) potential =
            expect (Math.PMFIter.iter kernel m s) charge +
              expect (Math.PMFIter.iter kernel (m + 1) s) potential := by
        rw [Math.PMFIter.iter_succ', expect_bind, hinner, expect_sub]
        ring
      linarith

/-- A solution of the transient Poisson equation that vanishes on the core
is nonnegative. -/
theorem poissonPotential_nonneg
    [Finite S] [Nonempty S]
    {kernel : S → PMF S} {core : Set S} {potential : S → ℝ}
    (hcore : potential ∈ coreVanishingSubmodule core)
    (hpoisson : ∀ s,
      potential s - expect (kernel s) potential =
        transientCharge core s) :
    ∀ s, 0 ≤ potential s := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  obtain ⟨smin, -, hmin⟩ :=
    Finset.exists_min_image Finset.univ potential Finset.univ_nonempty
  intro s
  by_contra hs
  have hslt : potential s < 0 := lt_of_not_ge hs
  have hminlt : potential smin < 0 :=
    (hmin s (Finset.mem_univ s)).trans_lt hslt
  have hsminNotCore : smin ∉ core := by
    intro hsCore
    rw [hcore hsCore] at hminlt
    exact lt_irrefl 0 hminlt
  have hminExpect :
      potential smin ≤ expect (kernel smin) potential := by
    simpa using expect_mono (kernel smin)
      (fun _ => potential smin) potential
      (fun u => hmin u (Finset.mem_univ u))
  have hp := hpoisson smin
  rw [transientCharge_of_not_mem hsminNotCore] at hp
  linarith

/-- A nonnegative core-vanishing function is bounded in expectation by its
sup norm times the transient probability. -/
theorem expect_le_norm_mul_transientProbability
    [Fintype S]
    (d : PMF S) (core : Set S) (f : S → ℝ)
    (hfcore : f ∈ coreVanishingSubmodule core)
    (hfnonneg : ∀ s, 0 ≤ f s) :
    expect d f ≤ ‖f‖ * expect d (transientCharge core) := by
  calc
    expect d f ≤ expect d (fun s => ‖f‖ * transientCharge core s) := by
      apply expect_mono
      intro s
      by_cases hs : s ∈ core
      · simp [transientCharge, hs, hfcore hs]
      · simpa [transientCharge, hs, Real.norm_eq_abs,
          abs_of_nonneg (hfnonneg s)] using norm_le_pi_norm f s
    _ = ‖f‖ * expect d (transientCharge core) :=
      expect_const_mul d ‖f‖ (transientCharge core)

/-- A nonnegative Poisson potential obeys the geometric block estimate
`‖h‖∞ ≤ m / δ`. -/
theorem poissonPotential_norm_le_div
    [Fintype S] [Nonempty S]
    {kernel : S → PMF S} {core : Set S} {potential : S → ℝ}
    {m : ℕ} {δ : ℝ}
    (hδpos : 0 < δ) (hδone : δ ≤ 1)
    (hreach : HasUniformCoreReach kernel core m δ)
    (hcore : potential ∈ coreVanishingSubmodule core)
    (hpoisson : ∀ s,
      potential s - expect (kernel s) potential =
        transientCharge core s)
    (hnonneg : ∀ s, 0 ≤ potential s) :
    ‖potential‖ ≤ (m : ℝ) / δ := by
  have hpoint (s : S) :
      potential s ≤ (m : ℝ) + ‖potential‖ * (1 - δ) := by
    rw [poissonPotential_eq_sum_expect_add_expect_iter hpoisson m s]
    have hsum :
        (∑ t ∈ Finset.range m,
          expect (Math.PMFIter.iter kernel t s)
            (transientCharge core)) ≤ (m : ℝ) := by
      calc
        (∑ t ∈ Finset.range m,
            expect (Math.PMFIter.iter kernel t s)
              (transientCharge core)) ≤
            ∑ _t ∈ Finset.range m, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t _
          simpa using expect_mono
            (Math.PMFIter.iter kernel t s)
            (transientCharge core) (fun _ => 1)
            (transientCharge_le_one core)
        _ = (m : ℝ) := by simp
    have htail :
        expect (Math.PMFIter.iter kernel m s) potential ≤
          ‖potential‖ * (1 - δ) := by
      calc
        expect (Math.PMFIter.iter kernel m s) potential ≤
            ‖potential‖ *
              expect (Math.PMFIter.iter kernel m s)
                (transientCharge core) :=
          expect_le_norm_mul_transientProbability
            (Math.PMFIter.iter kernel m s) core potential hcore hnonneg
        _ ≤ ‖potential‖ * (1 - δ) :=
          mul_le_mul_of_nonneg_left (hreach s) (norm_nonneg _)
    linarith
  have hnorm :
      ‖potential‖ ≤ (m : ℝ) + ‖potential‖ * (1 - δ) := by
    rw [pi_norm_le_iff_of_nonneg]
    · intro s
      simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg s)] using hpoint s
    · positivity
  apply (le_div_iff₀ hδpos).2
  nlinarith

/-- A finite-state closed core with a uniform finite-step reach margin admits
a nonnegative hitting-time/Poisson potential, vanishing on the core and
bounded by `m / δ`. -/
theorem exists_nonnegative_poissonPotential_of_uniformCoreReach
    [Fintype S] [Nonempty S]
    {kernel : S → PMF S} {core : Set S}
    (hclosed : IsClosedCore kernel core)
    {m : ℕ} {δ : ℝ}
    (hδpos : 0 < δ) (hδone : δ ≤ 1)
    (hreach : HasUniformCoreReach kernel core m δ) :
    ∃ potential : S → ℝ,
      (∀ s, 0 ≤ potential s) ∧
      (∀ ⦃s⦄, s ∈ core → potential s = 0) ∧
      (∀ s,
        potential s - expect (kernel s) potential =
          transientCharge core s) ∧
      ‖potential‖ ≤ (m : ℝ) / δ := by
  obtain ⟨h, hh⟩ := exists_coreVanishing_poissonPotential
    hclosed hδpos hδone hreach
  let potential : S → ℝ := h
  have hpoisson : ∀ s,
      potential s - expect (kernel s) potential =
        transientCharge core s := by
    intro s
    have hs := congrFun (congrArg Subtype.val hh) s
    change
      (h : S → ℝ) s -
          (killedMarkovOperator kernel core hclosed h : S → ℝ) s =
        transientCharge core s at hs
    simpa [potential, killedMarkovOperator_apply] using hs
  have hnonneg : ∀ s, 0 ≤ potential s :=
    poissonPotential_nonneg h.property hpoisson
  refine ⟨potential, hnonneg, h.property, hpoisson, ?_⟩
  exact poissonPotential_norm_le_div
    hδpos hδone hreach h.property hpoisson hnonneg

end

end Math.Probability
