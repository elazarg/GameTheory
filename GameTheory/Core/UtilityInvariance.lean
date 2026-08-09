/-
# Utility-scale invariance

Positive affine changes to each player's outcome utility preserve every
expected-utility comparison.  This file records the immediate Nash and
dominance consequences at the canonical `GameForm` layer.

The theorem family is adapted from
`reference/GameTheory-v1/GameTheory/Concepts/Foundations/UtilityInvariance.lean`
at commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.  The successor statements
apply to arbitrary stochastic game forms rather than rebuilding a deterministic
expected-utility game wrapper.
-/

import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

variable {ι : Type uι} [DecidableEq ι] {F : GameForm ι}

/-- Per-player positive affine changes of outcome utility preserve Nash
equilibrium in every game form. -/
theorem isNash_affine (utility : F.sig.Outcome → ι → ℝ)
    (scale shift : ι → ℝ) (hscale : ∀ who, 0 < scale who)
    (profile : Profile F.sig) :
    IsNash F (euPreference utility) profile ↔
      IsNash F (euPreference (affineUtility utility scale shift)) profile := by
  rw [isNash_iff, isNash_iff]
  refine forall_congr' fun who => forall_congr' fun replacement => ?_
  exact (euPreference_affine utility hscale who _ _).symm

/-- Per-player positive affine changes of outcome utility preserve dominant
strategies in every game form. -/
theorem isDominant_affine (utility : F.sig.Outcome → ι → ℝ)
    (scale shift : ι → ℝ) (hscale : ∀ who, 0 < scale who)
    (who : ι) (strategy : F.sig.Strategy who) :
    IsDominant F (euPreference utility) who strategy ↔
      IsDominant F (euPreference (affineUtility utility scale shift)) who strategy := by
  unfold IsDominant WeaklyDominates
  refine forall_congr' fun alternative => forall_congr' fun profile => ?_
  exact (euPreference_affine utility hscale who _ _).symm

/-- Adding a player-specific constant to outcome utility preserves Nash
equilibrium. -/
theorem isNash_shift (utility : F.sig.Outcome → ι → ℝ) (shift : ι → ℝ)
    (profile : Profile F.sig) :
    IsNash F (euPreference utility) profile ↔
      IsNash F (euPreference fun outcome who => utility outcome who + shift who)
        profile := by
  have hutility :
      (fun outcome who => utility outcome who + shift who) =
        affineUtility utility (fun _ => 1) shift := by
    funext outcome who
    simp [affineUtility]
  rw [hutility]
  exact isNash_affine utility (fun _ => 1) shift (fun _ => one_pos) profile

/-- Multiplying every player's outcome utility by the same positive scalar
preserves Nash equilibrium. -/
theorem isNash_scale (utility : F.sig.Outcome → ι → ℝ) (scale : ℝ)
    (hscale : 0 < scale) (profile : Profile F.sig) :
    IsNash F (euPreference utility) profile ↔
      IsNash F (euPreference fun outcome who => scale * utility outcome who)
        profile := by
  have hutility :
      (fun outcome who => scale * utility outcome who) =
        affineUtility utility (fun _ => scale) (fun _ => 0) := by
    funext outcome who
    simp [affineUtility]
  rw [hutility]
  exact isNash_affine utility (fun _ => scale) (fun _ => 0)
    (fun _ => hscale) profile

end GameTheory
