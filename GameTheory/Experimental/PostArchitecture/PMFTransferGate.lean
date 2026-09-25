/-
EXP-131: PMF-mixture transfer and the integration boundary.
-/

import GameTheory.Core.MixtureSimulation
import GameTheory.Experimental.PostArchitecture.PMFStaticGate

noncomputable section

namespace GameTheory.Experimental.PMFTransferGate

open GameTheory GameTheory.GameForm GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration

abbrev sourceSignature : GameSignature Unit where
  Strategy _ := ℕ
  Outcome := ℕ

abbrev targetSignature : GameSignature Unit where
  Strategy _ := Option ℕ
  Outcome := ℕ

abbrev source : GameForm Unit where
  sig := sourceSignature
  play profile := PMF.pure (profile ())

abbrev target : GameForm Unit where
  sig := targetSignature
  play profile := match profile () with
    | some n => PMF.pure n
    | none => geometric.map Nat.succ

def sourceProfile : Profile source.sig := fun _ => 0

def compile (_ : Unit) (n : ℕ) : Option ℕ := some n

/-- The extra target action is the infinite geometric mixture of positive
source actions. This certificate is independent of the utility. -/
def mixture : MixtureSimulationOn source target id id (fun _ _ => True) where
  compileStrategy := compile
  honest_law profile := by
    simp [source, target, compile, Profile.map, PMF.map_id]
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    cases who
    cases replacement with
    | none =>
        refine ⟨geometric.map Nat.succ, ?_⟩
        simp [source, target, Profile.update_same,
          PMF.map_id, PMF.bind_pure]
    | some n =>
        refine ⟨PMF.pure n, ?_⟩
        simp [source, target, Profile.update_same, PMF.map_id]

def linearLoss : ℕ → Unit → ℝ
  | 0, _ => 0
  | n + 1, _ => -((n : ℝ) + 1)

def explodingLoss : ℕ → Unit → ℝ
  | 0, _ => 0
  | n + 1, _ => -exploding n

theorem linearLoss_succ (n : ℕ) :
    linearLoss (Nat.succ n) () = -PMFStaticGate.linearUtility n 0 := by
  simp [linearLoss, PMFStaticGate.linearUtility]

theorem explodingLoss_succ (n : ℕ) :
    explodingLoss (Nat.succ n) () = -exploding n := by
  simp [explodingLoss]

theorem target_none_play (profile : Profile target.sig) :
    target.play (Profile.update profile () none) = geometric.map Nat.succ := by
  simp [target, Profile.update_same]

theorem source_zero_nash (utility : ℕ → Unit → ℝ)
    (hbest : ∀ n, utility n () ≤ utility 0 ()) :
    IsNash source (euPreference utility) sourceProfile := by
  rw [isNash_iff]
  intro who replacement
  cases who
  have hpoint := (euPreference_pure_iff utility () 0 replacement).mpr
    (hbest replacement)
  simpa only [source, sourceProfile, Profile.update_same] using hpoint

theorem linear_source_nash :
    IsNash source (euPreference linearLoss) sourceProfile := by
  apply source_zero_nash
  intro n
  cases n with
  | zero => exact le_rfl
  | succ n =>
      simp only [linearLoss]
      linarith [Nat.cast_nonneg (α := ℝ) n]

theorem exploding_source_nash :
    IsNash source (euPreference explodingLoss) sourceProfile := by
  apply source_zero_nash
  intro n
  cases n with
  | zero => exact le_rfl
  | succ n =>
      simp only [explodingLoss]
      have hnonneg : 0 ≤ exploding n := by unfold exploding; positivity
      linarith

/-- The positive-utility reading integrates every target deviation, including
the infinite-support action `none`. -/
theorem linear_target_deviation_integrable (who : Unit)
    (replacement : Option ℕ) :
    UtilityIntegrable linearLoss who
      (target.play (Profile.update
        (mixture.compileProfile sourceProfile) who replacement)) := by
  cases who
  cases replacement with
  | some n =>
      simpa [target, Profile.update_same] using
        (payoffIntegrable_pure n (fun outcome => linearLoss outcome ()))
  | none =>
      have hlinear := PMFStaticGate.linearUtility_integrable_geometric
      have hneg := payoffIntegrable_neg hlinear
      have hmap : PayoffIntegrable (geometric.map Nat.succ)
          (fun outcome => linearLoss outcome ()) := by
        apply (payoffIntegrable_map_iff Nat.succ geometric _).mpr
        apply payoffIntegrable_congr_on_support (hf := hneg)
        intro n _
        exact (linearLoss_succ n).symm
      rw [target_none_play]
      exact hmap

/-- The public mixture iff transfers the source equilibrium because all
actual target deviations integrate under the linear loss. -/
theorem linear_target_nash :
    IsNash target (euPreference linearLoss)
      (mixture.compileProfile sourceProfile) := by
  apply (mixture.isNash_compileProfile_iff linearLoss sourceProfile
    (fun _ _ => trivial)).mpr
  exact ⟨linear_source_nash, linear_target_deviation_integrable⟩

theorem exploding_every_source_deviation_integrable (n : ℕ) :
    UtilityIntegrable explodingLoss ()
      (source.play (Profile.update sourceProfile () n)) := by
  simpa [source, Profile.update_same] using
    (payoffIntegrable_pure n (fun outcome => explodingLoss outcome ()))

private theorem exploding_map_not_integrable :
    ¬ PayoffIntegrable (geometric.map Nat.succ)
      (fun outcome => explodingLoss outcome ()) := by
  intro hmap
  have hsource : PayoffIntegrable geometric
      (fun n => explodingLoss (Nat.succ n) ()) :=
    (payoffIntegrable_map_iff Nat.succ geometric
      (fun outcome => explodingLoss outcome ())).mp hmap
  have hpositive : UtilityIntegrable PMFStaticGate.explodingUtility 0 geometric := by
    have hneg := payoffIntegrable_neg hsource
    apply payoffIntegrable_congr_on_support (hf := hneg)
    intro n _
    simp [explodingLoss_succ, PMFStaticGate.explodingUtility]
  exact PMFStaticGate.explodingUtility_not_integrable hpositive

/-- The added target action has divergent absolute payoff even though each
source pure deviation has a defined, nonimproving payoff. -/
theorem exploding_none_not_integrable :
    ¬ UtilityIntegrable explodingLoss ()
      (target.play (Profile.update
        (mixture.compileProfile sourceProfile) () none)) := by
  rw [target_none_play]
  exact exploding_map_not_integrable

theorem exploding_target_not_nash :
    ¬ IsNash target (euPreference explodingLoss)
      (mixture.compileProfile sourceProfile) := by
  intro htarget
  have hguards := (mixture.isNash_compileProfile_iff explodingLoss sourceProfile
    (fun _ _ => trivial)).mp htarget
  exact exploding_none_not_integrable (hguards.2 () none)

end GameTheory.Experimental.PMFTransferGate
