/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Knowledge.CommonKnowledge

/-!
# Approximate Common Knowledge

Monderer--Samet style common `p`-belief over the finite partition model in
`CommonKnowledge.lean`.  Like `CommonKnowledge.posterior`, the core definitions
are algebraic over a real-valued prior; `IsPositivePrior` and
`IsProbabilityThreshold` record the semantic side conditions used by the
bridge theorems.

The definitions are deliberately stated on top of the existing real-valued
`posterior` API:

* `PBelief` is the event where one agent assigns probability at least `p`;
* `mutualPBelief` is simultaneous `p`-belief by every agent;
* `IsPEvident` is an event that, whenever true, everyone `p`-believes;
* `CommonPBeliefAt` uses the standard finite witness formulation: an event is
  common `p`-belief at a state when some `p`-evident event containing that state
  is contained in mutual `p`-belief of the target event.
* `commonPBelief_posterior_reports_close` is the Monderer--Samet quantitative
  agreement theorem: common `p`-belief of posterior reports makes reports differ
  by at most `2 * (1 - p)`.

The final section provides a small certificate lemma for downstream
coordination examples: once a game-specific payoff/rationality argument
produces the Monderer--Samet witness event, common `p`-belief follows.
-/

namespace GameTheory

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω]

/-- Semantic side condition for the real-valued prior used by `posterior`. -/
def IsPositivePrior (μ : Ω → ℝ) : Prop :=
  ∀ s, μ s > 0

/-- Semantic side condition for a probability threshold. -/
def IsProbabilityThreshold (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1

private noncomputable def eventMass (μ : Ω → ℝ) (S : Finset Ω) : ℝ :=
  ∑ ω ∈ S, μ ω

private theorem eventMass_decomp_cells (μ : Ω → ℝ) (P : InfoPartition Ω) (S : Finset Ω) :
    eventMass μ S = ∑ C ∈ (Finset.univ.image P.cell), eventMass μ (C ∩ S) := by
  unfold eventMass
  have hU : IsSelfEvident P (Finset.univ : Finset Ω) := by
    intro _ _ t _
    exact Finset.mem_univ t
  have h := selfEvident_sum_decomp P (F := (Finset.univ : Finset Ω)) hU
    (fun t => if t ∈ S then μ t else 0)
  simpa [Finset.sum_filter, Finset.mem_inter, and_left_comm, and_assoc] using h

omit [Fintype Ω] [DecidableEq Ω] in
private theorem eventMass_mono (μ : Ω → ℝ) (hμ : IsPositivePrior μ)
    {S T : Finset Ω} (hST : S ⊆ T) : eventMass μ S ≤ eventMass μ T := by
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (by intro x _ _; exact le_of_lt (hμ x))

omit [Fintype Ω] [DecidableEq Ω] in
private theorem eventMass_nonneg (μ : Ω → ℝ) (hμ : IsPositivePrior μ) (S : Finset Ω) :
    0 ≤ eventMass μ S := by
  unfold eventMass
  exact Finset.sum_nonneg (fun x _ => le_of_lt (hμ x))

omit [Fintype Ω] [DecidableEq Ω] in
private theorem eventMass_pos_of_nonempty (μ : Ω → ℝ) (hμ : IsPositivePrior μ)
    {S : Finset Ω} (hS : S.Nonempty) : 0 < eventMass μ S := by
  unfold eventMass
  exact Finset.sum_pos (fun x _ => hμ x) hS

omit [Fintype Ω] in
private theorem eventMass_inter_add_sdiff (μ : Ω → ℝ) (C A : Finset Ω) :
    eventMass μ (C ∩ A) + eventMass μ (C \ A) = eventMass μ C := by
  unfold eventMass
  rw [← Finset.sum_union]
  · have hset : C ∩ A ∪ C \ A = C := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · intro h
        rcases h with h | h <;> exact h.1
      · intro hxC
        by_cases hxA : x ∈ A
        · exact Or.inl ⟨hxC, hxA⟩
        · exact Or.inr ⟨hxC, hxA⟩
    rw [hset]
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hx1 hx2
    exact hx2.2 hx1.2

/-- The event where partition `P` assigns posterior at least `p` to `E`. -/
noncomputable def PBelief (μ : Ω → ℝ) (P : InfoPartition Ω)
    (p : ℝ) (E : Finset Ω) : Finset Ω :=
  Finset.univ.filter fun s => posterior μ P E s ≥ p

@[simp]
theorem mem_PBelief_iff (μ : Ω → ℝ) (P : InfoPartition Ω)
    (p : ℝ) (E : Finset Ω) (s : Ω) :
    s ∈ PBelief μ P p E ↔ posterior μ P E s ≥ p := by
  simp [PBelief]

/-- Lowering the threshold only enlarges a `p`-belief event. -/
theorem PBelief_mono_threshold (μ : Ω → ℝ) (P : InfoPartition Ω)
    {p q : ℝ} (hpq : p ≤ q) (E : Finset Ω) :
    PBelief μ P q E ⊆ PBelief μ P p E := by
  intro s hs
  rw [mem_PBelief_iff] at hs ⊢
  exact le_trans hpq hs

private theorem PBelief_mono_event (μ : Ω → ℝ) (hμ : IsPositivePrior μ)
    (P : InfoPartition Ω) (p : ℝ) {E F : Finset Ω} (hEF : E ⊆ F) :
    PBelief μ P p E ⊆ PBelief μ P p F := by
  intro s hs
  rw [mem_PBelief_iff] at hs ⊢
  unfold posterior at hs ⊢
  have hden_pos : 0 < ∑ t ∈ P.cell s, μ t :=
    Finset.sum_pos (fun t _ => hμ t) ⟨s, P.reflexive s⟩
  have hnum : (∑ t ∈ P.cell s ∩ E, μ t) ≤ ∑ t ∈ P.cell s ∩ F, μ t := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hEF (Finset.mem_inter.mp hx).2⟩)
      (by intro x _ _; exact le_of_lt (hμ x))
  exact le_trans hs ((div_le_div_iff_of_pos_right hden_pos).2 hnum)

private theorem PBelief_cell_inter_nonempty (μ : Ω → ℝ) (hμ : IsPositivePrior μ)
    (P : InfoPartition Ω) {p : ℝ} (hp : 0 < p) {E : Finset Ω} {s : Ω}
    (hs : s ∈ PBelief μ P p E) :
    (P.cell s ∩ E).Nonempty := by
  rw [mem_PBelief_iff] at hs
  unfold posterior at hs
  have hden_pos : 0 < ∑ t ∈ P.cell s, μ t :=
    Finset.sum_pos (fun t _ => hμ t) ⟨s, P.reflexive s⟩
  have hnum_pos : 0 < ∑ t ∈ P.cell s ∩ E, μ t := by
    have hmul : p * (∑ t ∈ P.cell s, μ t) ≤ ∑ t ∈ P.cell s ∩ E, μ t :=
      (le_div_iff₀ hden_pos).1 hs
    nlinarith [mul_pos hp hden_pos]
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  rw [hempty, Finset.sum_empty] at hnum_pos
  linarith

private theorem posterior_eq_of_mem_PBelief_const (μ : Ω → ℝ) (hμ : IsPositivePrior μ)
    (P : InfoPartition Ω) {p : ℝ} (hp : 0 < p) {C E : Finset Ω} {r : ℝ} {s : Ω}
    (hs : s ∈ PBelief μ P p C)
    (hC : ∀ t ∈ C, posterior μ P E t = r) :
    posterior μ P E s = r := by
  obtain ⟨t, ht⟩ := PBelief_cell_inter_nonempty μ hμ P hp hs
  rw [Finset.mem_inter] at ht
  rw [posterior_eq_of_same_cell μ P E s t ht.1]
  exact hC t ht.2

private theorem PBelief_of_PBelief_subset_PBelief (μ : Ω → ℝ) (hμ : IsPositivePrior μ)
    (P : InfoPartition Ω) {p : ℝ} (hp : 0 < p) {A C : Finset Ω} {s : Ω}
    (hs : s ∈ PBelief μ P p A) (hA : A ⊆ PBelief μ P p C) :
    s ∈ PBelief μ P p C := by
  rw [mem_PBelief_iff]
  obtain ⟨t, ht⟩ := PBelief_cell_inter_nonempty μ hμ P hp hs
  rw [Finset.mem_inter] at ht
  have htC := hA ht.2
  rw [mem_PBelief_iff] at htC
  rw [posterior_eq_of_same_cell μ P C s t ht.1]
  exact htC

/-- Mutual `p`-belief: every agent assigns probability at least `p` to `E`. -/
noncomputable def mutualPBelief [Fintype ι]
    (μ : Ω → ℝ) (P : ι → InfoPartition Ω)
    (p : ℝ) (E : Finset Ω) : Finset Ω :=
  Finset.univ.filter fun s => ∀ i : ι, s ∈ PBelief μ (P i) p E

@[simp]
theorem mem_mutualPBelief_iff [Fintype ι]
    (μ : Ω → ℝ) (P : ι → InfoPartition Ω)
    (p : ℝ) (E : Finset Ω) (s : Ω) :
    s ∈ mutualPBelief μ P p E ↔
      ∀ i : ι, posterior μ (P i) E s ≥ p := by
  simp [mutualPBelief]

theorem mutualPBelief_mono_threshold [Fintype ι]
    (μ : Ω → ℝ) (P : ι → InfoPartition Ω)
    {p q : ℝ} (hpq : p ≤ q) (E : Finset Ω) :
    mutualPBelief μ P q E ⊆ mutualPBelief μ P p E := by
  intro s hs
  rw [mem_mutualPBelief_iff] at hs ⊢
  intro i
  exact le_trans hpq (hs i)

/-- A `p`-evident event: whenever `F` occurs, every agent assigns probability
at least `p` to `F`. -/
def IsPEvident [Fintype ι]
    (μ : Ω → ℝ) (P : ι → InfoPartition Ω)
    (p : ℝ) (F : Finset Ω) : Prop :=
  ∀ i : ι, F ⊆ PBelief μ (P i) p F

theorem IsPEvident.mono_threshold [Fintype ι]
    {μ : Ω → ℝ} {P : ι → InfoPartition Ω}
    {p q : ℝ} (hpq : p ≤ q) {F : Finset Ω}
    (hF : IsPEvident μ P q F) :
    IsPEvident μ P p F := by
  intro i s hs
  exact PBelief_mono_threshold μ (P i) hpq F (hF i hs)

/-- Common `p`-belief at a state, in the Monderer--Samet finite witness form. -/
def CommonPBeliefAt [Fintype ι]
    (μ : Ω → ℝ) (P : ι → InfoPartition Ω)
    (p : ℝ) (E : Finset Ω) (s : Ω) : Prop :=
  ∃ F : Finset Ω,
    s ∈ F ∧ IsPEvident μ P p F ∧ F ⊆ mutualPBelief μ P p E

/-- The event of states at which `E` is common `p`-belief. -/
noncomputable def CommonPBelief [Fintype ι]
    (μ : Ω → ℝ) (P : ι → InfoPartition Ω)
    (p : ℝ) (E : Finset Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter fun s => CommonPBeliefAt μ P p E s

theorem mem_CommonPBelief_iff [Fintype ι]
    (μ : Ω → ℝ) (P : ι → InfoPartition Ω)
    (p : ℝ) (E : Finset Ω) (s : Ω) :
    s ∈ CommonPBelief μ P p E ↔ CommonPBeliefAt μ P p E s := by
  classical
  simp [CommonPBelief]

theorem CommonPBeliefAt.implies_mutualPBelief [Fintype ι]
    {μ : Ω → ℝ} {P : ι → InfoPartition Ω}
    {p : ℝ} {E : Finset Ω} {s : Ω}
    (h : CommonPBeliefAt μ P p E s) :
    s ∈ mutualPBelief μ P p E := by
  rcases h with ⟨F, hsF, _hEvident, hFbelief⟩
  exact hFbelief hsF

theorem CommonPBeliefAt.mono_threshold [Fintype ι]
    {μ : Ω → ℝ} {P : ι → InfoPartition Ω}
    {p q : ℝ} (hpq : p ≤ q) {E : Finset Ω} {s : Ω}
    (h : CommonPBeliefAt μ P q E s) :
    CommonPBeliefAt μ P p E s := by
  rcases h with ⟨F, hsF, hEvident, hFbelief⟩
  refine ⟨F, hsF, hEvident.mono_threshold hpq, ?_⟩
  exact hFbelief.trans (mutualPBelief_mono_threshold μ P hpq E)

private lemma commonPBelief_atom_real_arith {x α r p δ : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hα_le_1 : α ≤ 1) (hp_le_α : p ≤ α)
    (hδ0 : 0 ≤ δ) (hδ_ub : δ ≤ 1 - α) (heq : r = x * α + δ) :
    |x - r| ≤ 1 - p := by
  have h1 : (0 : ℝ) ≤ 1 - α := by linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [mul_le_mul_of_nonneg_right hx1 h1, mul_nonneg hx0 h1]

private theorem commonPBelief_atom_bound
    (μ : Ω → ℝ) (hμ : IsPositivePrior μ)
    (P : InfoPartition Ω) {p r : ℝ} {A E C : Finset Ω}
    (hAev : A ⊆ PBelief μ P p A)
    (hAR : ∀ ω ∈ A, posterior μ P E ω = r)
    (hC : C ∈ Finset.univ.image P.cell)
    (hAC_pos : 0 < eventMass μ (C ∩ A)) :
    |eventMass μ ((C ∩ E) ∩ A) / eventMass μ (C ∩ A) - r| ≤ 1 - p := by
  rcases Finset.mem_image.mp hC with ⟨z, _hz, rfl⟩
  have hAC_nonempty : (P.cell z ∩ A).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hAC_pos
    have := eventMass_nonneg μ hμ (∅ : Finset Ω)
    unfold eventMass at this hAC_pos
    simp at hAC_pos
  rcases hAC_nonempty with ⟨ω, hω⟩
  rw [Finset.mem_inter] at hω
  have hcellω : P.cell ω = P.cell z := P.coherent z ω hω.1
  have hC_pos : 0 < eventMass μ (P.cell z) :=
    eventMass_pos_of_nonempty μ hμ ⟨z, P.reflexive z⟩
  have hEA_le_A : eventMass μ ((P.cell z ∩ E) ∩ A) ≤ eventMass μ (P.cell z ∩ A) := by
    exact eventMass_mono μ hμ (by
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      exact ⟨(Finset.mem_inter.mp hx.1).1, hx.2⟩)
  have hEA_le_E : eventMass μ ((P.cell z ∩ E) ∩ A) ≤ eventMass μ (P.cell z ∩ E) := by
    exact eventMass_mono μ hμ (by
      intro x hx
      exact (Finset.mem_inter.mp hx).1)
  have hA_le_C : eventMass μ (P.cell z ∩ A) ≤ eventMass μ (P.cell z) := by
    exact eventMass_mono μ hμ Finset.inter_subset_left
  have hE_eq : eventMass μ (P.cell z ∩ E) = r * eventMass μ (P.cell z) := by
    have hpost := hAR ω hω.2
    unfold posterior at hpost
    rw [hcellω] at hpost
    change eventMass μ (P.cell z ∩ E) / eventMass μ (P.cell z) = r at hpost
    field_simp [hC_pos.ne'] at hpost
    simpa [mul_comm] using hpost
  have hp_le_alpha : p ≤ eventMass μ (P.cell z ∩ A) / eventMass μ (P.cell z) := by
    have hbelief := hAev hω.2
    rw [mem_PBelief_iff] at hbelief
    unfold posterior at hbelief
    rw [hcellω] at hbelief
    change eventMass μ (P.cell z ∩ A) / eventMass μ (P.cell z) ≥ p at hbelief
    exact hbelief
  have hdelta_le : eventMass μ (P.cell z ∩ E) - eventMass μ ((P.cell z ∩ E) ∩ A)
      ≤ eventMass μ (P.cell z) - eventMass μ (P.cell z ∩ A) := by
    have hEdec := eventMass_inter_add_sdiff μ (P.cell z ∩ E) A
    have hCdec := eventMass_inter_add_sdiff μ (P.cell z) A
    have hnot_le : eventMass μ ((P.cell z ∩ E) \ A) ≤ eventMass μ (P.cell z \ A) := by
      exact eventMass_mono μ hμ (by
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨(Finset.mem_inter.mp hx.1).1, hx.2⟩)
    linarith
  have hcond : eventMass μ ((P.cell z ∩ E) ∩ A) / eventMass μ (P.cell z ∩ A)
      ∈ Set.Icc (0 : ℝ) 1 := by
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · exact div_nonneg (eventMass_nonneg μ hμ _) hAC_pos.le
    · exact (div_le_one hAC_pos).2 hEA_le_A
  have hδ0 : 0 ≤ (eventMass μ (P.cell z ∩ E) - eventMass μ ((P.cell z ∩ E) ∩ A)) /
      eventMass μ (P.cell z) := by
    exact div_nonneg (sub_nonneg.mpr hEA_le_E) hC_pos.le
  have hδub : (eventMass μ (P.cell z ∩ E) - eventMass μ ((P.cell z ∩ E) ∩ A)) /
      eventMass μ (P.cell z)
        ≤ 1 - eventMass μ (P.cell z ∩ A) / eventMass μ (P.cell z) := by
    have hrewrite : 1 - eventMass μ (P.cell z ∩ A) / eventMass μ (P.cell z)
        = (eventMass μ (P.cell z) - eventMass μ (P.cell z ∩ A)) /
            eventMass μ (P.cell z) := by
      field_simp [hC_pos.ne']
    rw [hrewrite]
    exact div_le_div_of_nonneg_right hdelta_le hC_pos.le
  have heq : r =
      (eventMass μ ((P.cell z ∩ E) ∩ A) / eventMass μ (P.cell z ∩ A)) *
          (eventMass μ (P.cell z ∩ A) / eventMass μ (P.cell z)) +
        (eventMass μ (P.cell z ∩ E) - eventMass μ ((P.cell z ∩ E) ∩ A)) /
          eventMass μ (P.cell z) := by
    have hCne : eventMass μ (P.cell z) ≠ 0 := hC_pos.ne'
    have hAne : eventMass μ (P.cell z ∩ A) ≠ 0 := hAC_pos.ne'
    rw [show r = eventMass μ (P.cell z ∩ E) / eventMass μ (P.cell z) by
      rw [hE_eq]; field_simp [hCne]]
    field_simp [hCne, hAne]
    ring
  exact commonPBelief_atom_real_arith hcond.1 hcond.2
    ((div_le_one hC_pos).2 hA_le_C) hp_le_alpha hδ0 hδub heq

private theorem commonPBelief_core_bound
    (μ : Ω → ℝ) (hμ : IsPositivePrior μ)
    (P : InfoPartition Ω) {p r : ℝ} {A E : Finset Ω}
    (hAne : A.Nonempty)
    (hAev : A ⊆ PBelief μ P p A)
    (hAR : ∀ ω ∈ A, posterior μ P E ω = r) :
    |r - eventMass μ (A ∩ E) / eventMass μ A| ≤ 1 - p := by
  let cells : Finset (Finset Ω) := Finset.univ.image P.cell
  have hApos : 0 < eventMass μ A := eventMass_pos_of_nonempty μ hμ hAne
  have hA_decomp : eventMass μ A = ∑ C ∈ cells, eventMass μ (C ∩ A) := by
    simpa [cells] using eventMass_decomp_cells μ P A
  have hAE_decomp : eventMass μ (A ∩ E) =
      ∑ C ∈ cells, eventMass μ ((C ∩ E) ∩ A) := by
    calc eventMass μ (A ∩ E)
        = ∑ C ∈ cells, eventMass μ (C ∩ (A ∩ E)) := by
            simpa [cells] using eventMass_decomp_cells μ P (A ∩ E)
      _ = ∑ C ∈ cells, eventMass μ ((C ∩ E) ∩ A) := by
            refine Finset.sum_congr rfl (fun C hC => ?_)
            rw [Finset.inter_assoc]
            congr 1
            ext x
            simp [and_assoc, and_comm]
  have hweighted : |r * eventMass μ A - eventMass μ (A ∩ E)|
      ≤ eventMass μ A * (1 - p) := by
    calc |r * eventMass μ A - eventMass μ (A ∩ E)|
        = |∑ C ∈ cells, (r * eventMass μ (C ∩ A) - eventMass μ ((C ∩ E) ∩ A))| := by
            rw [hA_decomp, hAE_decomp, Finset.mul_sum, ← Finset.sum_sub_distrib]
      _ ≤ ∑ C ∈ cells, |r * eventMass μ (C ∩ A) - eventMass μ ((C ∩ E) ∩ A)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ C ∈ cells, eventMass μ (C ∩ A) * (1 - p) := by
            refine Finset.sum_le_sum (fun C hC => ?_)
            by_cases hACpos : 0 < eventMass μ (C ∩ A)
            · have hbound := commonPBelief_atom_bound μ hμ P hAev hAR hC hACpos
              rw [abs_sub_comm] at hbound
              have hACne : eventMass μ (C ∩ A) ≠ 0 := hACpos.ne'
              have hACnonneg : 0 ≤ eventMass μ (C ∩ A) := eventMass_nonneg μ hμ _
              have hterm :
                  |r * eventMass μ (C ∩ A) - eventMass μ ((C ∩ E) ∩ A)|
                    = eventMass μ (C ∩ A) *
                        |r - eventMass μ ((C ∩ E) ∩ A) / eventMass μ (C ∩ A)| := by
                rw [show r * eventMass μ (C ∩ A) - eventMass μ ((C ∩ E) ∩ A)
                    = eventMass μ (C ∩ A) *
                        (r - eventMass μ ((C ∩ E) ∩ A) / eventMass μ (C ∩ A)) by
                  field_simp [hACne]]
                rw [abs_mul, abs_of_pos hACpos]
              rw [hterm]
              exact mul_le_mul_of_nonneg_left hbound hACnonneg
            · have hACnonpos : eventMass μ (C ∩ A) ≤ 0 := le_of_not_gt hACpos
              have hACzero : eventMass μ (C ∩ A) = 0 :=
                le_antisymm hACnonpos (eventMass_nonneg μ hμ _)
              have hEA_le_A : eventMass μ ((C ∩ E) ∩ A) ≤ eventMass μ (C ∩ A) := by
                exact eventMass_mono μ hμ (by
                  intro x hx
                  rw [Finset.mem_inter] at hx ⊢
                  exact ⟨(Finset.mem_inter.mp hx.1).1, hx.2⟩)
              have hEAzero : eventMass μ ((C ∩ E) ∩ A) = 0 := by
                exact le_antisymm (by simpa [hACzero] using hEA_le_A) (eventMass_nonneg μ hμ _)
              have hEAzero' : eventMass μ (C ∩ (E ∩ A)) = 0 := by
                simpa [Finset.inter_assoc, Finset.inter_comm, Finset.inter_left_comm]
                  using hEAzero
              simp [hACzero, hEAzero']
      _ = eventMass μ A * (1 - p) := by
            rw [← Finset.sum_mul, ← hA_decomp]
  have hscaled : |r - eventMass μ (A ∩ E) / eventMass μ A| ≤ 1 - p := by
    have hAne' : eventMass μ A ≠ 0 := hApos.ne'
    have hrewrite : r - eventMass μ (A ∩ E) / eventMass μ A =
        (r * eventMass μ A - eventMass μ (A ∩ E)) / eventMass μ A := by
      field_simp [hAne']
    rw [hrewrite, abs_div, abs_of_pos hApos]
    have hweighted' : |r * eventMass μ A - eventMass μ (A ∩ E)|
        ≤ (1 - p) * eventMass μ A := by
      simpa [mul_comm] using hweighted
    exact (div_le_iff₀ hApos).2 hweighted'
  simpa [abs_sub_comm] using hscaled

/-! ## Approximate agreement -/

/-- **Monderer--Samet approximate agreement.** If it is common `p`-belief that
each player `i` reports posterior `r i` for event `E`, then any two reports are
within `2 * (1 - p)`.

This is the finite `InfoPartition` analogue of the common-`p`-belief agreement
bound formalized in Axiom Math's Lean development accompanying
"We Can't Agree to Disagree, Formally: Aumann's Theorem and Assumption
Accounting in Lean", https://dx.doi.org/10.2139/ssrn.6837298. -/
theorem commonPBelief_posterior_reports_close [Fintype ι]
    {μ : Ω → ℝ} (hμ : IsPositivePrior μ)
    {P : ι → InfoPartition Ω} {E : Finset Ω} {s : Ω}
    {p : ℝ} (hp : 0 < p) {r : ι → ℝ}
    (h : CommonPBeliefAt μ P p
      (Finset.univ.filter fun ω => ∀ i : ι, posterior μ (P i) E ω = r i) s) :
    ∀ i j, |r i - r j| ≤ 2 * (1 - p) := by
  intro i j
  rcases h with ⟨A₀, hsA₀, hA₀ev, hA₀bel⟩
  let C : Finset Ω := Finset.univ.filter fun ω => ∀ k : ι, posterior μ (P k) E ω = r k
  let A : Finset Ω := PBelief μ (P i) p A₀ ∩ PBelief μ (P j) p A₀
  have hA₀A : A₀ ⊆ A := by
    intro ω hω
    rw [Finset.mem_inter]
    exact ⟨hA₀ev i hω, hA₀ev j hω⟩
  have hAne : A.Nonempty := ⟨s, hA₀A hsA₀⟩
  have hAi_ev : A ⊆ PBelief μ (P i) p A := by
    intro ω hω
    rw [Finset.mem_inter] at hω
    exact PBelief_mono_event μ hμ (P i) p hA₀A hω.1
  have hAj_ev : A ⊆ PBelief μ (P j) p A := by
    intro ω hω
    rw [Finset.mem_inter] at hω
    exact PBelief_mono_event μ hμ (P j) p hA₀A hω.2
  have hAiC : A ⊆ PBelief μ (P i) p C := by
    intro ω hω
    rw [Finset.mem_inter] at hω
    exact PBelief_of_PBelief_subset_PBelief μ hμ (P i) hp hω.1 (by
      intro t ht
      have htmut := hA₀bel ht
      rw [mem_mutualPBelief_iff] at htmut
      rw [mem_PBelief_iff]
      exact htmut i)
  have hAjC : A ⊆ PBelief μ (P j) p C := by
    intro ω hω
    rw [Finset.mem_inter] at hω
    exact PBelief_of_PBelief_subset_PBelief μ hμ (P j) hp hω.2 (by
      intro t ht
      have htmut := hA₀bel ht
      rw [mem_mutualPBelief_iff] at htmut
      rw [mem_PBelief_iff]
      exact htmut j)
  have hri : ∀ ω ∈ A, posterior μ (P i) E ω = r i := by
    intro ω hω
    exact posterior_eq_of_mem_PBelief_const μ hμ (P i) hp (hAiC hω)
      (fun t ht => by
        change t ∈ Finset.univ.filter
          (fun ω => ∀ k : ι, posterior μ (P k) E ω = r k) at ht
        rw [Finset.mem_filter] at ht
        exact ht.2 i)
  have hrj : ∀ ω ∈ A, posterior μ (P j) E ω = r j := by
    intro ω hω
    exact posterior_eq_of_mem_PBelief_const μ hμ (P j) hp (hAjC hω)
      (fun t ht => by
        change t ∈ Finset.univ.filter
          (fun ω => ∀ k : ι, posterior μ (P k) E ω = r k) at ht
        rw [Finset.mem_filter] at ht
        exact ht.2 j)
  have bound_i := commonPBelief_core_bound μ hμ (P i) hAne hAi_ev hri
  have bound_j := commonPBelief_core_bound μ hμ (P j) hAne hAj_ev hrj
  have tri := abs_sub_le (r i) (eventMass μ (A ∩ E) / eventMass μ A) (r j)
  rw [abs_sub_comm] at bound_j
  linarith

/-! ## Bridges from exact common knowledge -/

omit [Fintype Ω] in
theorem posterior_eq_one_of_cell_subset
    (μ : Ω → ℝ) (hμ : ∀ s, μ s > 0)
    (P : InfoPartition Ω) {E : Finset Ω} {s : Ω}
    (hcell : P.cell s ⊆ E) :
    posterior μ P E s = 1 := by
  unfold posterior
  rw [Finset.inter_eq_left.mpr hcell, div_self]
  exact ne_of_gt (Finset.sum_pos (fun t _ => hμ t) ⟨s, P.reflexive s⟩)

theorem IsSelfEvident.isPEvident [Fintype ι]
    {μ : Ω → ℝ} (hμ : ∀ s, μ s > 0)
    {P : ι → InfoPartition Ω} {p : ℝ} (hp : p ≤ 1)
    {F : Finset Ω} (hF : ∀ i, IsSelfEvident (P i) F) :
    IsPEvident μ P p F := by
  intro i s hs
  rw [mem_PBelief_iff]
  rw [posterior_self_evident μ hμ (P i) F s hs (hF i)]
  exact hp

/-- Exact common knowledge implies common `p`-belief for every `p ≤ 1`,
under a strictly positive prior. -/
theorem CommonKnowledgeAt.commonPBeliefAt [Fintype ι]
    {μ : Ω → ℝ} (hμ : IsPositivePrior μ)
    {P : ι → InfoPartition Ω} {E : Finset Ω} {s : Ω}
    {p : ℝ} (hp : p ≤ 1)
    (hCK : CommonKnowledgeAt P E s) :
    CommonPBeliefAt μ P p E s := by
  rcases hCK with ⟨F, hFE, hsF, hSelf⟩
  refine ⟨F, hsF, IsSelfEvident.isPEvident hμ hp hSelf, ?_⟩
  intro t htF
  rw [mem_mutualPBelief_iff]
  intro i
  have hcellF : (P i).cell t ⊆ F := hSelf i t htF
  have hcellE : (P i).cell t ⊆ E := hcellF.trans hFE
  rw [posterior_eq_one_of_cell_subset μ hμ (P i) hcellE]
  exact hp

/-! ## Abstract coordination certificates -/

/-- Compatibility name for `CommonPBeliefAt`, used when a concrete
coordination-game survival argument is viewed as producing a certificate.

Concrete coordination-game files should prove this predicate from their
payoff and rationality assumptions. -/
abbrev CommonPBeliefCertificate [Fintype ι]
    (μ : Ω → ℝ) (P : ι → InfoPartition Ω)
    (p : ℝ) (E : Finset Ω) (s : Ω) : Prop :=
  CommonPBeliefAt μ P p E s

/-- A game-specific common-`p`-belief certificate is exactly the witness needed
for `CommonPBeliefAt`.  This is the reusable target for later payoff-level
survival proofs; it is not itself a payoff theorem. -/
theorem CommonPBeliefCertificate.commonPBeliefAt [Fintype ι]
    {μ : Ω → ℝ} {P : ι → InfoPartition Ω}
    {p : ℝ} {E : Finset Ω} {s : Ω}
    (h : CommonPBeliefCertificate μ P p E s) :
    CommonPBeliefAt μ P p E s := h

/-- Abstract necessity wrapper: if a model-specific survival predicate implies
the common-`p`-belief certificate, then survival implies common `p`-belief. -/
theorem survives_only_if_commonPBelief_certificate [Fintype ι]
    {μ : Ω → ℝ} {P : ι → InfoPartition Ω}
    {p : ℝ} {E : Finset Ω} {Survives : Ω → Prop}
    (hcert : ∀ s, Survives s → CommonPBeliefCertificate μ P p E s)
    {s : Ω} (hs : Survives s) :
    CommonPBeliefAt μ P p E s :=
  (hcert s hs).commonPBeliefAt

end GameTheory
