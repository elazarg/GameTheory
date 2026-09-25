/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators

namespace GameTheory.Math.Probability

universe uι uA uB

set_option autoImplicit false

/-- The dependent product sum identity for a finite ordinal index. -/
theorem ENNReal_tsum_pi_fin {n : ℕ} {A : Fin n → Type uA}
    (g : (i : Fin n) → A i → ENNReal) :
    ∑' s : ((i : Fin n) → A i), ∏ i, g i (s i) = ∏ i, ∑' a : A i, g i a := by
  induction n with
  | zero =>
    let h_unique : Unique ((i : Fin 0) → A i) := Pi.uniqueOfIsEmpty _
    rw [tsum_eq_single default (fun s hs => absurd (h_unique.eq_default s) hs)]
    simp [Finset.prod_eq_one (fun (i : Fin 0) _ => Fin.elim0 i)]
  | succ n ih =>
    let e : A 0 × ((i : Fin n) → A i.succ) ≃ ((i : Fin (n + 1)) → A i) :=
      Fin.consEquiv A
    rw [← e.tsum_eq (f := fun s => ∏ i, g i (s i))]
    rw [ENNReal.tsum_prod']
    have h_split : ∀ (a₀ : A 0) (s' : (i : Fin n) → A i.succ),
        (∏ i, g i (e (a₀, s') i)) =
          g 0 a₀ * ∏ i, g i.succ (s' i) := by
      intro a₀ s'
      have he_val : ∀ i : Fin (n + 1), e (a₀, s') i = Fin.cons a₀ s' i := by
        intro i
        rfl
      simp_rw [he_val]
      rw [Fin.prod_univ_succ (f := fun i => g i (Fin.cons a₀ s' i))]
      simp [Fin.cons_zero, Fin.cons_succ]
    simp_rw [h_split]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]
    rw [Fin.prod_univ_succ (f := fun i => ∑' a, g i a)]

/-- Sum a finite product of nonnegative weights over all dependent assignments. -/
theorem ENNReal_tsum_pi {ι : Type uι} [Fintype ι] {A : ι → Type uA}
    (g : (i : ι) → A i → ENNReal) :
    ∑' s : ((i : ι) → A i), ∏ i, g i (s i) = ∏ i, ∑' a : A i, g i a := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let ePi : ((j : Fin (Fintype.card ι)) → A (e j)) ≃ ((i : ι) → A i) :=
    Equiv.piCongrLeft A e
  rw [← ePi.tsum_eq (f := fun s => ∏ i, g i (s i))]
  have h_prod : ∀ t : ((j : Fin (Fintype.card ι)) → A (e j)),
      (∏ i : ι, g i (ePi t i)) = ∏ j, g (e j) (t j) := by
    intro t
    rw [← e.prod_comp (g := fun i => g i (ePi t i))]
    apply Finset.prod_congr rfl
    intro j _
    show g (e j) (ePi t (e j)) = g (e j) (t j)
    rw [show (ePi t (e j) : A (e j)) = t j from
      Equiv.piCongrLeft_apply_apply A e t j]
  simp_rw [h_prod]
  have hfin := ENNReal_tsum_pi_fin (A := fun j => A (e j))
    (g := fun j a => g (e j) a)
  rw [hfin, ← e.prod_comp (g := fun i => ∑' a : A i, g i a)]

/-- The independent product of finitely many arbitrary PMFs. -/
noncomputable def independentProduct {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} (μ : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  ⟨fun s => ∏ i, μ i (s i), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [ENNReal_tsum_pi]
    simp [PMF.tsum_coe]⟩

@[simp]
theorem independentProduct_apply {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} (μ : ∀ i, PMF (A i)) (s : ∀ i, A i) :
    independentProduct μ s = ∏ i, μ i (s i) := rfl

theorem independentProduct_support_iff {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} (μ : ∀ i, PMF (A i)) (s : ∀ i, A i) :
    s ∈ (independentProduct μ).support ↔ ∀ i, s i ∈ (μ i).support := by
  classical
  simp [independentProduct_apply, PMF.mem_support_iff, Finset.prod_ne_zero_iff]

theorem independentProduct_pure {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} (s : ∀ i, A i) :
    independentProduct (fun i => (PMF.pure (s i) : PMF (A i))) = PMF.pure s := by
  classical
  ext t
  by_cases h : t = s
  · subst h
    simp [independentProduct_apply]
  · have hcoords : ∃ i, t i ≠ s i := by
      by_contra hn
      have hn' : ∀ i, t i = s i := fun i =>
        Classical.not_not.mp (not_exists.mp hn i)
      apply h
      funext i
      exact hn' i
    obtain ⟨i, hi⟩ := hcoords
    have hzero : (∏ j, if t j = s j then (1 : ENNReal) else 0) = 0 := by
      rw [Finset.prod_eq_zero_iff]
      exact ⟨i, Finset.mem_univ i, by simp [hi]⟩
    simpa [independentProduct_apply, h] using hzero

/-- Mapping every coordinate commutes with the independent product. -/
theorem independentProduct_map {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} {B : ι → Type uB} (μ : ∀ i, PMF (A i))
    (f : ∀ i, A i → B i) :
    (independentProduct μ).map (fun s i => f i (s i)) =
      independentProduct (fun i => (μ i).map (f i)) := by
  classical
  ext t
  rw [PMF.map_apply]
  have hfactor (s : ∀ i, A i) :
      (@ite ENNReal (t = fun i => f i (s i)) (Classical.propDecidable _)
        (∏ i, μ i (s i)) 0) =
        ∏ i, if t i = f i (s i) then μ i (s i) else 0 := by
    by_cases h : t = fun i => f i (s i)
    · subst h
      simp
    · have hcoords : ∃ i, t i ≠ f i (s i) := by
        by_contra hn
        have hall : ∀ i, t i = f i (s i) := fun i =>
          Classical.not_not.mp (not_exists.mp hn i)
        exact h (funext hall)
      obtain ⟨i, hi⟩ := hcoords
      have hzero : (∏ i, if t i = f i (s i) then μ i (s i) else 0) = 0 := by
        rw [Finset.prod_eq_zero_iff]
        exact ⟨i, Finset.mem_univ i, by simp [hi]⟩
      simp [h, hzero]
  simp only [independentProduct_apply]
  calc
    (∑' s : (∀ i, A i),
      @ite ENNReal (t = fun i => f i (s i)) (Classical.propDecidable _)
        (∏ i, μ i (s i)) 0) =
        ∑' s : (∀ i, A i), ∏ i, if t i = f i (s i) then μ i (s i) else 0 :=
      tsum_congr hfactor
    _ = ∏ i, ∑' a, if t i = f i a then μ i a else 0 :=
      ENNReal_tsum_pi (g := fun i a => if t i = f i a then μ i a else 0)
    _ = ∏ i, (μ i).map (f i) (t i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (PMF.map_apply (f i) (μ i) (t i)).symm

/-- Reindexing the coordinates of a finite independent product. -/
theorem independentProduct_reindex {ι : Type uι} {κ : Type*}
    [Fintype ι] [Fintype κ] {A : ι → Type uA}
    (equiv : ι ≃ κ) (laws : ∀ i, PMF (A i)) :
    (independentProduct laws).map
        (Equiv.piCongrLeft A equiv.symm).symm =
      independentProduct (fun k => laws (equiv.symm k)) := by
  classical
  ext draw
  rw [PMF.map_apply]
  let source : ∀ i, A i := Equiv.piCongrLeft A equiv.symm draw
  rw [tsum_eq_single source]
  · have hsource : (Equiv.piCongrLeft A equiv.symm).symm source = draw :=
      (Equiv.piCongrLeft A equiv.symm).symm_apply_apply draw
    simp only [hsource, ite_true]
    rw [independentProduct_apply, independentProduct_apply]
    rw [← equiv.symm.prod_comp]
    apply Finset.prod_congr rfl
    intro k _
    exact congrArg (laws (equiv.symm k))
      (Equiv.piCongrLeft_apply_apply A equiv.symm draw k)
  · intro other hne
    have hneq : draw ≠ (Equiv.piCongrLeft A equiv.symm).symm other := by
      intro heq
      apply hne
      have h := congrArg (Equiv.piCongrLeft A equiv.symm) heq
      simpa [source] using h.symm
    simp [hneq]

private theorem product_split {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {A : ι → Type uA} (μ : ∀ i, PMF (A i)) (j : ι) (s : ∀ i, A i) :
    (∏ i, μ i (s i)) = μ j (s j) * ∏ i : {i // i ≠ j}, μ i (s i) := by
  classical
  rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset ι))
    (f := fun i => μ i (s i)) (a := j) (by simp)]
  congr 1
  exact Finset.prod_subtype (s := Finset.univ.erase j)
    (p := fun i : ι => i ≠ j) (by intro i; simp [Finset.mem_erase])
    (fun i => μ i (s i))

/-- A finite independent product factors into one selected coordinate and
an independent product of the rest. -/
theorem independentProduct_splitAt {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {A : ι → Type uA} (μ : ∀ i, PMF (A i)) (j : ι) :
    independentProduct μ =
      (μ j).bind (fun value =>
        (independentProduct (fun i : {i // i ≠ j} => μ i)).map
          (fun rest => (Equiv.piSplitAt j A).symm (value, rest))) := by
  classical
  ext s
  let e := Equiv.piSplitAt j A
  rw [PMF.bind_apply]
  simp_rw [PMF.map_apply, independentProduct_apply]
  simp_rw [← ENNReal.tsum_mul_left]
  simp_rw [mul_ite, mul_zero]
  rw [← ENNReal.tsum_prod' (f := fun p : A j ×
    ((i : {i // i ≠ j}) → A i) =>
      if s = e.symm p then μ j p.1 *
        ∏ i : {i // i ≠ j}, μ i (p.2 i) else 0)]
  rw [tsum_eq_single (e s)]
  · simp only [e.symm_apply_apply, ite_true]
    simp only [e, Equiv.piSplitAt_apply]
    exact product_split μ j s
  · intro p hp
    have hne : s ≠ e.symm p := by
      intro heq
      apply hp
      calc
        p = e (e.symm p) := (e.apply_symm_apply p).symm
        _ = e s := by rw [← heq]
    simp [hne]

private theorem indicator_independentProduct_rect {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} (μ : ∀ i, PMF (A i))
    (s : ∀ i, Set (A i)) (assignment : ∀ i, A i) :
    (Set.pi Set.univ s).indicator (independentProduct μ) assignment =
      ∏ i, (s i).indicator (μ i) (assignment i) := by
  classical
  by_cases hall : ∀ i, assignment i ∈ s i
  · have hmem : assignment ∈ Set.pi Set.univ s := fun i _ => hall i
    simp [hmem, hall, independentProduct_apply]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hnot : assignment ∉ Set.pi Set.univ s := by
      intro hmem
      exact hi (hmem i (Set.mem_univ i))
    simp only [Set.indicator_of_notMem hnot]
    symm
    rw [Finset.prod_eq_zero_iff]
    exact ⟨i, Finset.mem_univ i, Set.indicator_of_notMem hi (μ i)⟩

/-- The outer measure of a rectangle under a finite independent product is the
product of its coordinate masses. -/
theorem independentProduct_outerMeasure_pi {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} (μ : ∀ i, PMF (A i)) (s : ∀ i, Set (A i)) :
    (independentProduct μ).toOuterMeasure (Set.pi Set.univ s) =
      ∏ i, (μ i).toOuterMeasure (s i) := by
  rw [PMF.toOuterMeasure_apply]
  simp_rw [indicator_independentProduct_rect μ s]
  rw [ENNReal_tsum_pi]
  apply Finset.prod_congr rfl
  intro i hi
  rw [PMF.toOuterMeasure_apply]

/-- Projecting onto injectively selected coordinates preserves their
independent product law. The coordinate carriers need not be finite. -/
theorem independentProduct_map_embedding {ι : Type uι} {κ : Type*}
    [Fintype ι] [Fintype κ] {A : ι → Type uA}
    (e : κ ↪ ι) (laws : ∀ i, PMF (A i)) :
    (independentProduct laws).map (fun values k => values (e k)) =
      independentProduct (fun k => laws (e k)) := by
  classical
  apply PMF.ext
  intro target
  let C (i : ι) : Set (A i) := {value | ∀ k, e k = i →
    (⟨i, value⟩ : Sigma A) = ⟨e k, target k⟩}
  have hselected (k : κ) : C (e k) = {target k} := by
    ext value
    constructor
    · intro hall
      simpa [C] using hall k rfl
    · intro hequal other hother
      obtain rfl := e.injective hother
      simpa [C] using hequal
  have hother (i : ι) (hi : i ∉ Set.range e) : C i = Set.univ := by
    ext value
    simp only [C, Set.mem_univ, iff_true]
    intro k hk
    exact (hi ⟨k, hk⟩).elim
  have hevent : (fun (values : ∀ i, A i) k => values (e k)) ⁻¹' {target} =
      Set.pi Set.univ C := by
    ext values
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ,
      true_implies]
    constructor
    · intro hequal i k hk
      subst i
      exact congrArg (Sigma.mk (e k)) (congrFun hequal k)
    · intro hall
      exact funext fun k => by simpa [C] using hall (e k) k rfl
  calc
    (independentProduct laws).map (fun values k => values (e k)) target =
        ((independentProduct laws).map (fun values k => values (e k))).toOuterMeasure
          {target} := (PMF.toOuterMeasure_apply_singleton _ _).symm
    _ = (independentProduct laws).toOuterMeasure
          ((fun values k => values (e k)) ⁻¹' {target}) :=
      PMF.toOuterMeasure_map_apply _ _ _
    _ = ∏ i, (laws i).toOuterMeasure (C i) := by
      rw [hevent, independentProduct_outerMeasure_pi]
    _ = ∏ k, (laws (e k)).toOuterMeasure {target k} := by
      symm
      apply Fintype.prod_of_injective e e.injective
      · intro i hi
        rw [hother i hi]
        exact ((laws i).toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
      · intro k
        rw [hselected k]
    _ = independentProduct (fun k => laws (e k)) target := by
      rw [independentProduct_apply]
      simp only [PMF.toOuterMeasure_apply_singleton]

/-- Filtering an independent finite product on a rectangle filters every
coordinate independently. Coordinate carriers may be infinite. -/
theorem filter_independentProduct {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} (μ : ∀ i, PMF (A i))
    (s : ∀ i, Set (A i))
    (hcoord : ∀ i, ∃ a ∈ s i, a ∈ (μ i).support) :
    (independentProduct μ).filter (Set.pi Set.univ s) (by
      classical
      let assignment : ∀ i, A i := fun i => Classical.choose (hcoord i)
      refine ⟨assignment, ?_, ?_⟩
      · intro i _
        exact (Classical.choose_spec (hcoord i)).1
      · exact (independentProduct_support_iff μ assignment).2
          (fun i => (Classical.choose_spec (hcoord i)).2)) =
      independentProduct (fun i => (μ i).filter (s i) (hcoord i)) := by
  classical
  have hmass : (∑' assignment,
      (Set.pi Set.univ s).indicator (independentProduct μ) assignment) =
        ∏ i, ∑' a, (s i).indicator (μ i) a := by
    simp_rw [indicator_independentProduct_rect μ s]
    exact ENNReal_tsum_pi (fun i a => (s i).indicator (μ i) a)
  ext assignment
  rw [PMF.filter_apply, independentProduct_apply]
  simp_rw [PMF.filter_apply]
  rw [hmass, Finset.prod_mul_distrib]
  rw [indicator_independentProduct_rect μ s]
  have hpos (i : ι) :
      (∑' a, (s i).indicator (μ i) a) ≠ 0 := by
    obtain ⟨a, ha, hsupport⟩ := hcoord i
    intro hzero
    have hvalue := (ENNReal.tsum_eq_zero.mp hzero) a
    simp [ha] at hvalue
    exact hsupport hvalue
  rw [ENNReal.prod_inv_distrib (by
    intro i _ j _ _
    exact Or.inl (hpos i))]


/-- The evaluation of a finite independent product has its input marginal. -/
theorem independentProduct_map_eval {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} (μ : ∀ i, PMF (A i)) (j : ι) :
    (independentProduct μ).map (fun s => s j) = μ j := by
  classical
  ext b
  rw [PMF.map_apply]
  simp_rw [independentProduct_apply]
  let e := Equiv.piSplitAt j A
  rw [← e.symm.tsum_eq
    (f := fun s : (∀ i, A i) => if b = s j then ∏ i, μ i (s i) else 0)]
  have hrest :
      (∑' r : (∀ i : {i // i ≠ j}, A ↑i),
        ∏ i : {i // i ≠ j}, μ ↑i (r i)) = 1 := by
    rw [ENNReal_tsum_pi]
    simp [PMF.tsum_coe]
  have hinner (a : A j) :
      (∑' r : (∀ i : {i // i ≠ j}, A ↑i),
        if b = e.symm (a, r) j then
          ∏ i : ι, μ i (e.symm (a, r) i) else 0) =
        if b = a then μ j a else 0 := by
    calc
      (∑' r : (∀ i : {i // i ≠ j}, A ↑i),
          if b = e.symm (a, r) j then
            ∏ i : ι, μ i (e.symm (a, r) i) else 0) =
          ∑' r : (∀ i : {i // i ≠ j}, A ↑i), if b = a then μ j a *
            ∏ i : {i // i ≠ j}, μ ↑i (r i) else 0 := by
        apply tsum_congr
        intro r
        rw [product_split μ j (e.symm (a, r))]
        have hprod :
            (∏ i : {i // i ≠ j}, μ ↑i (e.symm (a, r) ↑i)) =
              ∏ i : {i // i ≠ j}, μ ↑i (r i) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [e, Equiv.piSplitAt, i.property]
        rw [show e.symm (a, r) j = a by simp [e, Equiv.piSplitAt], hprod]
      _ = if b = a then μ j a else 0 := by
        by_cases h : b = a
        · subst b
          simp only [ite_true]
          rw [ENNReal.tsum_mul_left, hrest]
          simp
        · simp [h]
  calc
    (∑' c : A j × (∀ i : {i // i ≠ j}, A ↑i),
        if b = e.symm c j then
          ∏ i : ι, μ i (e.symm c i) else 0) =
        ∑' a, ∑' r, if b = e.symm (a, r) j then
          ∏ i : ι, μ i (e.symm (a, r) i) else 0 := ENNReal.tsum_prod'
    _ = ∑' a, if b = a then μ j a else 0 := tsum_congr hinner
    _ = μ j b := by
      rw [tsum_eq_single b]
      · simp
      · intro a ha
        simp [Ne.symm ha]

/-- Independent kernels preserve coordinate independence under the product law. -/
theorem independentProduct_bind {ι : Type uι} [Fintype ι]
    {A : ι → Type uA} {B : ι → Type uB}
    (μ : ∀ i, PMF (A i)) (κ : ∀ i, A i → PMF (B i)) :
    (independentProduct μ).bind
        (fun s => independentProduct (fun i => κ i (s i))) =
      independentProduct (fun i => (μ i).bind (κ i)) := by
  classical
  ext t
  rw [PMF.bind_apply]
  simp only [independentProduct_apply]
  calc
    (∑' s : (∀ i, A i), (∏ i, μ i (s i)) *
        ∏ i, κ i (s i) (t i)) =
      ∑' s : (∀ i, A i), ∏ i, μ i (s i) * κ i (s i) (t i) := by
        apply tsum_congr
        intro s
        rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑' a, μ i a * κ i a (t i) :=
      ENNReal_tsum_pi (g := fun i a => μ i a * κ i a (t i))
    _ = ∏ i, (μ i).bind (κ i) (t i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (PMF.bind_apply (μ i) (κ i) (t i)).symm

end GameTheory.Math.Probability
