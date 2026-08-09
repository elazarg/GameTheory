/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ChargedPathSelection
import Mathlib.Data.Finset.Fold

/-!
# Finite-horizon maximal charge

For a charged relation with finitely many edge types, this file gives the exact
finite-horizon dynamic programme.  The empty path is included among the
competitors, so the value is always nonnegative.  The finite edge type is all
that is needed for the maximisation; the state type itself need not be finite.
No compactness or continuum-state attainment is claimed here: attainment is
only for the finite edge-type dynamic programme and its at-most-horizon paths.
-/

universe u v

namespace Math
namespace ChargedPathBudget
namespace ChargedRelation

variable {State : Type u} {Edge : Type v}
variable (R : ChargedRelation State Edge)
variable [DecidableEq State] [Fintype Edge]

/-! ## The dynamic programme -/

/-- The one-step competitors for a finite-horizon value. -/
def finiteHorizonCandidates (s : State) : Finset Edge :=
  Finset.univ.filter (fun e => R.src e = s)

/-- Maximum charge obtainable from `s` using at most `horizon` edges.

The recursive step folds `max` over the finitely many outgoing edges, with the
empty path represented by the initial value `0`. -/
def finiteHorizonMaxCharge (R : ChargedRelation State Edge) : State → ℕ → ℝ
  | _, 0 => 0
  | s, horizon + 1 =>
      (R.finiteHorizonCandidates s).fold max 0
        (fun e => R.charge e + finiteHorizonMaxCharge R (R.tgt e) horizon)

@[simp] theorem finiteHorizonMaxCharge_zero (s : State) :
    R.finiteHorizonMaxCharge s 0 = 0 := rfl

@[simp] theorem finiteHorizonMaxCharge_succ (s : State) (horizon : ℕ) :
    R.finiteHorizonMaxCharge s (horizon + 1) =
      (R.finiteHorizonCandidates s).fold max 0
        (fun e => R.charge e + R.finiteHorizonMaxCharge (R.tgt e) horizon) := rfl

/-- The defining Bellman recurrence, with the empty path explicit as the zero
competitor. -/
theorem finiteHorizonMaxCharge_recurrence (s : State) (horizon : ℕ) :
    R.finiteHorizonMaxCharge s (horizon + 1) =
      max 0
        ((R.finiteHorizonCandidates s).fold max 0
          (fun e => R.charge e + R.finiteHorizonMaxCharge (R.tgt e) horizon)) := by
  rw [R.finiteHorizonMaxCharge_succ]
  have hnonneg : 0 ≤
      (R.finiteHorizonCandidates s).fold max 0
        (fun e => R.charge e + R.finiteHorizonMaxCharge (R.tgt e) horizon) :=
    (Finset.le_fold_max (c := (0 : ℝ))).2 (Or.inl le_rfl)
  exact (max_eq_right hnonneg).symm

theorem finiteHorizonMaxCharge_nonneg (s : State) (horizon : ℕ) :
    0 ≤ R.finiteHorizonMaxCharge s horizon := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [R.finiteHorizonMaxCharge_succ]
      exact (Finset.le_fold_max (c := (0 : ℝ))).2 (Or.inl le_rfl)

private theorem candidate_le_finiteHorizonMaxCharge
    (s : State) (horizon : ℕ) {e : Edge}
    (he : e ∈ R.finiteHorizonCandidates s) :
    R.charge e + R.finiteHorizonMaxCharge (R.tgt e) horizon ≤
      R.finiteHorizonMaxCharge s (horizon + 1) := by
  rw [R.finiteHorizonMaxCharge_succ]
  exact (Finset.le_fold_max (c := (R.charge e +
    R.finiteHorizonMaxCharge (R.tgt e) horizon))).2
    (Or.inr ⟨e, he, le_rfl⟩)

/-! ## Upper bounds and exact witnesses -/

/-- Every path whose length is at most the horizon is bounded by the dynamic
programme value. -/
theorem chargeSum_le_finiteHorizonMaxCharge
    {s t : State} (p : R.Path s t) {horizon : ℕ}
    (hlen : p.length ≤ horizon) :
    p.chargeSum ≤ R.finiteHorizonMaxCharge s horizon := by
  induction horizon generalizing s t with
  | zero =>
      cases p with
      | nil => simp
      | cons e rest => simp at hlen
  | succ horizon ih =>
      cases p with
      | nil =>
          simpa using R.finiteHorizonMaxCharge_nonneg s (horizon + 1)
      | @cons e t rest =>
        have hrest : rest.length ≤ horizon := by
          simpa only [Path.length_cons] using (Nat.le_of_succ_le_succ hlen)
        have hcandidate : e ∈ R.finiteHorizonCandidates (R.src e) := by
          simp [finiteHorizonCandidates]
        have hnext := candidate_le_finiteHorizonMaxCharge
          R (R.src e) horizon hcandidate
        simp only [Path.chargeSum_cons]
        linarith [ih rest hrest]

/-- A finite-horizon maximum is attained by a literal admissible path (the
empty path is used when all outgoing competitors are nonpositive). -/
theorem exists_path_eq_finiteHorizonMaxCharge (s : State) (horizon : ℕ) :
    ∃ (t : State) (p : R.Path s t),
      p.length ≤ horizon ∧
      p.chargeSum = R.finiteHorizonMaxCharge s horizon := by
  induction horizon generalizing s with
  | zero =>
      exact ⟨s, Path.nil s, by simp, by simp⟩
  | succ horizon ih =>
      let M := R.finiteHorizonMaxCharge s (horizon + 1)
      by_cases hM : M = 0
      · exact ⟨s, Path.nil s, by simp, by simpa [M] using hM.symm⟩
      · have hMpos : 0 < M := lt_of_le_of_ne
          (R.finiteHorizonMaxCharge_nonneg s (horizon + 1)) (Ne.symm hM)
        have hfold : M ≤
            (R.finiteHorizonCandidates s).fold max 0
              (fun e => R.charge e +
                R.finiteHorizonMaxCharge (R.tgt e) horizon) := by
          rw [← R.finiteHorizonMaxCharge_succ]
        obtain ⟨e, he, hge⟩ :=
          (Finset.le_fold_max (c := M)).mp hfold |>.resolve_left
            (not_le_of_gt hMpos)
        obtain ⟨t, rest, hrest, hrestcharge⟩ := ih (R.tgt e)
        have hsrc : R.src e = s := (Finset.mem_filter.mp he).2
        cases hsrc
        let p : R.Path (R.src e) t := Path.cons e rest
        refine ⟨t, p, ?_, ?_⟩
        · simp [p]
          omega
        · change R.charge e + rest.chargeSum = M
          rw [hrestcharge]
          exact le_antisymm
            (candidate_le_finiteHorizonMaxCharge R (R.src e) horizon he) hge

theorem finiteHorizonMaxCharge_mono (s : State) :
    Monotone (R.finiteHorizonMaxCharge s) := by
  intro horizon₁ horizon₂ hle
  obtain ⟨t, p, hp, hcharge⟩ :=
    R.exists_path_eq_finiteHorizonMaxCharge s horizon₁
  exact hcharge ▸ R.chargeSum_le_finiteHorizonMaxCharge p (hp.trans hle)

/-! ## Unboundedness -/

/-- The horizon maxima from a state are unbounded above. -/
def HasUnboundedHorizonCharge (s : State) : Prop :=
  ∀ bound : ℝ, ∃ horizon : ℕ,
    bound ≤ R.finiteHorizonMaxCharge s horizon

theorem hasUnboundedFiniteCharge_iff_hasUnboundedHorizonCharge (s : State) :
    R.HasUnboundedFiniteCharge s ↔ R.HasUnboundedHorizonCharge s := by
  constructor
  · intro hfinite bound
    obtain ⟨t, p, hcharge⟩ := hfinite bound
    exact ⟨p.length, hcharge.trans
      (R.chargeSum_le_finiteHorizonMaxCharge p le_rfl)⟩
  · intro hh bound
    obtain ⟨horizon, hmax⟩ := hh bound
    obtain ⟨t, p, hlen, hcharge⟩ :=
      R.exists_path_eq_finiteHorizonMaxCharge s horizon
    exact ⟨t, p, hcharge ▸ hmax⟩

end ChargedRelation
end ChargedPathBudget
end Math
