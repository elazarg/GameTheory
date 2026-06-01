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

/-! ## Bridges from exact common knowledge -/

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

/-- A generic certificate produced by a concrete coordination-game survival
argument: there is a `p`-evident support event containing `s`, and throughout
that support the payoff-relevant event `E` is mutually `p`-believed.

Concrete coordination-game files should prove this predicate from their
payoff and rationality assumptions. -/
def CommonPBeliefCertificate [Fintype ι]
    (μ : Ω → ℝ) (P : ι → InfoPartition Ω)
    (p : ℝ) (E : Finset Ω) (s : Ω) : Prop :=
  ∃ F : Finset Ω,
    s ∈ F ∧ IsPEvident μ P p F ∧ F ⊆ mutualPBelief μ P p E

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
