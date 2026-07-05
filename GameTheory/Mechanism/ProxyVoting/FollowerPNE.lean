/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.Dynamics
import GameTheory.Mechanism.ProxyVoting.TieBreak

/-!
# Follower steering over the reachable pure-equilibrium set

Under non-monotone dynamics, better-response play from the truthful proxy state
can reach a pure Nash equilibrium whose outcome is not the true median (as in
Appendix A). When several equilibria are reachable, the outcome a follower faces
depends on which the proxies settle into, raising the question whether a follower
can misreport their position to move the *set of reachable equilibria* in their
favour.

This file provides the framework and the real-report obstruction:

* `BetterResponseStep` / `ReachesFromTruth` — the non-deterministic
  better-response reachability relation from the truthful state.
* `IsReachablePNEOutcome` — an outcome realized at some reachable equilibrium.
* `FollowerCannotBestCaseSteer` / `FollowerCannotWorstCaseSteer` — the two
  precise readings of "no follower benefits", as `Prop`s over the reachable set.
* `followerCannotBestCaseSteer_of_peak_reachable` — a sufficient condition for
  the best-case reading.
* `realTruthMinusTwo_gridPNE_not_realPNE` /
  `realMisreportOne_gridPNE_not_realPNE` — over `ℝ`, states that are pure
  equilibria among integer reports are not pure equilibria: each admits a
  non-integer better response.

Restricting reports to integers is what makes those states look like equilibria;
over `ℝ` the misreport side exhibits the same open-cell creep as the convergence
counterexamples (`Example3`, `minimaxTrap`). The worst-case steering question
over unbounded reports is not resolved here.
-/

namespace GameTheory

namespace ProxyVoting

variable {P F : Type*} [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F]
variable {pp : P → ℝ} {q : F → ℝ}

/-! ## Better-response reachability from the truthful state -/

/-- One step of the non-deterministic better-response dynamics: some proxy makes
a better response. -/
def BetterResponseStep (pp : P → ℝ) (q : F → ℝ) (s s' : P → ℝ) : Prop :=
  ∃ j r, IsBetterResponse pp q s j r ∧ s' = Function.update s j r

/-- A proxy state reachable from the truthful state `pp` by a (possibly empty)
sequence of better-response steps. -/
def ReachesFromTruth (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) : Prop :=
  Relation.ReflTransGen (BetterResponseStep pp q) pp s

/-- An outcome realized at some reachable pure Nash equilibrium. -/
def IsReachablePNEOutcome (pp : P → ℝ) (q : F → ℝ) (O : ℝ) : Prop :=
  ∃ s, ReachesFromTruth pp q s ∧ IsPNE pp q s ∧ outcome s q = O

theorem reachesFromTruth_refl (pp : P → ℝ) (q : F → ℝ) : ReachesFromTruth pp q pp :=
  Relation.ReflTransGen.refl

theorem ReachesFromTruth.tail_step {s s' : P → ℝ}
    (h : ReachesFromTruth pp q s) (hstep : BetterResponseStep pp q s s') :
    ReachesFromTruth pp q s' :=
  Relation.ReflTransGen.tail h hstep

theorem ReachesFromTruth.of_betterResponse {s : P → ℝ} {j : P} {r : ℝ}
    (h : ReachesFromTruth pp q s) (hbr : IsBetterResponse pp q s j r) :
    ReachesFromTruth pp q (Function.update s j r) :=
  h.tail_step ⟨j, r, hbr, rfl⟩

/-! ## Basic equilibrium facts -/

/-- A report at the population median pins the outcome to the median. -/
theorem outcome_eq_socialMedian_of_report_at {s : P → ℝ} {k : P}
    (hk : s k = socialMedian s q) : outcome s q = socialMedian s q := by
  have hd := delegate_dist_le s (socialMedian s q) k
  rw [hk, sub_self, abs_zero] at hd
  have := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
  simpa [outcome, winner] using this

/-- If the truthful state is already an equilibrium, its outcome is a reachable
equilibrium outcome. -/
theorem isReachablePNEOutcome_truth (h : IsPNE pp q pp) :
    IsReachablePNEOutcome pp q (outcome pp q) :=
  ⟨pp, reachesFromTruth_refl pp q, h, rfl⟩

/-- If the truthful proxy state is already a pure equilibrium, it is the only
state reachable from truth by strict better-response steps. -/
theorem reachesFromTruth_eq_truth_of_isPNE {s : P → ℝ} (h : IsPNE pp q pp)
    (hr : ReachesFromTruth pp q s) :
    s = pp := by
  induction hr with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      rcases hstep with ⟨j, r, hbr, -⟩
      exact absurd hbr (h j r)

/-! ## The two precise readings of "no follower can steer" -/

variable [DecidableEq F]

/-- The follower cannot improve the *closest* reachable equilibrium: for every
misreport and every equilibrium reachable under it, the truthful profile has a
reachable equilibrium at least as close to the follower's true position. -/
def FollowerCannotBestCaseSteer (pp : P → ℝ) (q : F → ℝ) (i : F) : Prop :=
  ∀ (x O' : ℝ), IsReachablePNEOutcome pp (Function.update q i x) O' →
    ∃ O, IsReachablePNEOutcome pp q O ∧ |O - q i| ≤ |O' - q i|

/-- The follower cannot improve the *worst* reachable equilibrium: for every
misreport and every equilibrium reachable under the truthful profile, the
misreported profile still has a reachable equilibrium at least as far from the
follower's true position. -/
def FollowerCannotWorstCaseSteer (pp : P → ℝ) (q : F → ℝ) (i : F) : Prop :=
  ∀ (x O : ℝ), IsReachablePNEOutcome pp q O →
    ∃ O', IsReachablePNEOutcome pp (Function.update q i x) O' ∧ |O - q i| ≤ |O' - q i|

/-- A provable sub-case: if the follower's true position is itself a reachable
equilibrium outcome (they already get their peak), no misreport can bring a
reachable equilibrium strictly closer — best-case steering is impossible. -/
theorem followerCannotBestCaseSteer_of_peak_reachable {i : F}
    (h : IsReachablePNEOutcome pp q (q i)) :
    FollowerCannotBestCaseSteer pp q i := by
  intro x O' _
  refine ⟨q i, h, ?_⟩
  rw [sub_self, abs_zero]
  exact abs_nonneg _

/-- Worst-case steering refutation criterion.  If one truthful reachable
equilibrium outcome is strictly farther from follower `i`'s true position than
every reachable equilibrium outcome under some misreport, then the worst-case
no-steering property is false. -/
theorem not_followerCannotWorstCaseSteer_of_strictly_closer_misreport {i : F}
    {x O : ℝ} (hO : IsReachablePNEOutcome pp q O)
    (hclose : ∀ O', IsReachablePNEOutcome pp (Function.update q i x) O' →
      |O' - q i| < |O - q i|) :
    ¬ FollowerCannotWorstCaseSteer pp q i := by
  intro h
  obtain ⟨O', hO', hfar⟩ := h x O hO
  exact not_le.mpr (hclose O' hO') hfar

/-! ## Integer-report states need not be equilibria over ℝ

For the peaks and followers below, the integer states are pure equilibria only
when reports are restricted to integers; over `ℝ` each admits a nearby
non-integer better response, so the integer-restricted steering pattern is a
discretization artifact.
-/

noncomputable def realWitnessPeaks : Fin 3 → ℝ
  | 0 => -4
  | 1 => 4
  | 2 => 4

noncomputable def realWitnessFollowers : Fin 3 → ℝ
  | 0 => 3
  | 1 => -2
  | 2 => 0

noncomputable def realTruthMinusTwoState : Fin 3 → ℝ
  | 0 => -4
  | 1 => -3
  | 2 => -2

noncomputable def realTruthOffGridState : Fin 3 → ℝ
  | 0 => -4
  | 1 => -3
  | 2 => -19 / 10

private theorem realTruthMinusTwo_cum_neg4 :
    Math.cumWeight (allPos realTruthMinusTwoState realWitnessFollowers)
      (fun _ => 1) (-4) = 1 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realTruthMinusTwoState realWitnessFollowers a ≤ -4)
        = ({Sum.inl (0 : Fin 3)} : Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realTruthMinusTwoState]; try norm_num)
    | inr i =>
        fin_cases i <;> (simp [allPos, realWitnessFollowers]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realTruthMinusTwo_cum_neg3 :
    Math.cumWeight (allPos realTruthMinusTwoState realWitnessFollowers)
      (fun _ => 1) (-3) = 2 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realTruthMinusTwoState realWitnessFollowers a ≤ -3)
        = ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} :
          Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realTruthMinusTwoState]; try norm_num)
    | inr i =>
        fin_cases i <;> (simp [allPos, realWitnessFollowers]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realTruthMinusTwo_cum_neg2 :
    Math.cumWeight (allPos realTruthMinusTwoState realWitnessFollowers)
      (fun _ => 1) (-2) = 4 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realTruthMinusTwoState realWitnessFollowers a ≤ -2)
        = ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3),
            Sum.inl (2 : Fin 3), Sum.inr (1 : Fin 3)} :
          Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realTruthMinusTwoState]; try norm_num)
    | inr i =>
        fin_cases i <;> (simp [allPos, realWitnessFollowers]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realTruthMinusTwo_socialMedian :
    socialMedian realTruthMinusTwoState realWitnessFollowers = -2 := by
  classical
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr
      ⟨Sum.inl (2 : Fin 3), Finset.mem_univ _, by
        simp [allPos, realTruthMinusTwoState]⟩
  · rw [realTruthMinusTwo_cum_neg2]
    norm_num [Math.totalWeight]
  · intro z hz hlt
    rcases Finset.mem_image.mp hz with ⟨a, -, rfl⟩
    cases a with
    | inl i =>
        fin_cases i
        · change 2 *
            Math.cumWeight (allPos realTruthMinusTwoState realWitnessFollowers)
              (fun _ => 1) (-4)
              < Math.totalWeight (fun _ : Fin 3 ⊕ Fin 3 => 1)
          rw [realTruthMinusTwo_cum_neg4]
          norm_num [Math.totalWeight]
        · change 2 *
            Math.cumWeight (allPos realTruthMinusTwoState realWitnessFollowers)
              (fun _ => 1) (-3)
              < Math.totalWeight (fun _ : Fin 3 ⊕ Fin 3 => 1)
          rw [realTruthMinusTwo_cum_neg3]
          norm_num [Math.totalWeight]
        · norm_num [allPos, realTruthMinusTwoState] at hlt
    | inr i =>
        fin_cases i <;> norm_num [allPos, realWitnessFollowers] at hlt

private theorem realTruthMinusTwo_outcome :
    outcome realTruthMinusTwoState realWitnessFollowers = -2 := by
  have hk : realTruthMinusTwoState (2 : Fin 3)
      = socialMedian realTruthMinusTwoState realWitnessFollowers := by
    rw [realTruthMinusTwo_socialMedian]
    norm_num [realTruthMinusTwoState]
  rw [outcome_eq_socialMedian_of_report_at hk, realTruthMinusTwo_socialMedian]

private theorem realTruthOffGrid_cum_neg4 :
    Math.cumWeight (allPos realTruthOffGridState realWitnessFollowers)
      (fun _ => 1) (-4) = 1 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realTruthOffGridState realWitnessFollowers a ≤ -4)
        = ({Sum.inl (0 : Fin 3)} : Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realTruthOffGridState]; try norm_num)
    | inr i =>
        fin_cases i <;> (simp [allPos, realWitnessFollowers]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realTruthOffGrid_cum_neg3 :
    Math.cumWeight (allPos realTruthOffGridState realWitnessFollowers)
      (fun _ => 1) (-3) = 2 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realTruthOffGridState realWitnessFollowers a ≤ -3)
        = ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} :
          Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realTruthOffGridState]; try norm_num)
    | inr i =>
        fin_cases i <;> (simp [allPos, realWitnessFollowers]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realTruthOffGrid_cum_neg2 :
    Math.cumWeight (allPos realTruthOffGridState realWitnessFollowers)
      (fun _ => 1) (-2) = 3 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realTruthOffGridState realWitnessFollowers a ≤ -2)
        = ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3),
            Sum.inr (1 : Fin 3)} : Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realTruthOffGridState]; try norm_num)
    | inr i =>
        fin_cases i <;> (simp [allPos, realWitnessFollowers]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realTruthOffGrid_socialMedian :
    socialMedian realTruthOffGridState realWitnessFollowers = -2 := by
  classical
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr
      ⟨Sum.inr (1 : Fin 3), Finset.mem_univ _, by
        simp [allPos, realWitnessFollowers]⟩
  · rw [realTruthOffGrid_cum_neg2]
    norm_num [Math.totalWeight]
  · intro z hz hlt
    rcases Finset.mem_image.mp hz with ⟨a, -, rfl⟩
    cases a with
    | inl i =>
        fin_cases i
        · change 2 *
            Math.cumWeight (allPos realTruthOffGridState realWitnessFollowers)
              (fun _ => 1) (-4)
              < Math.totalWeight (fun _ : Fin 3 ⊕ Fin 3 => 1)
          rw [realTruthOffGrid_cum_neg4]
          norm_num [Math.totalWeight]
        · change 2 *
            Math.cumWeight (allPos realTruthOffGridState realWitnessFollowers)
              (fun _ => 1) (-3)
              < Math.totalWeight (fun _ : Fin 3 ⊕ Fin 3 => 1)
          rw [realTruthOffGrid_cum_neg3]
          norm_num [Math.totalWeight]
        · norm_num [allPos, realTruthOffGridState] at hlt
    | inr i =>
        fin_cases i <;> norm_num [allPos, realWitnessFollowers] at hlt

private theorem realTruthOffGrid_outcome :
    outcome realTruthOffGridState realWitnessFollowers = -19 / 10 := by
  unfold outcome winner
  rw [realTruthOffGrid_socialMedian]
  have hdel : delegate realTruthOffGridState (-2) = (2 : Fin 3) := by
    refine delegate_eq_of_forall_lt (s := realTruthOffGridState) ?_
    intro j hj
    fin_cases j <;> simp [realTruthOffGridState] at hj ⊢ <;> norm_num
  simp [hdel, realTruthOffGridState]

private theorem realTruthOffGridState_eq_update :
    Function.update realTruthMinusTwoState (2 : Fin 3) (-19 / 10)
      = realTruthOffGridState := by
  funext j
  fin_cases j <;> simp [realTruthMinusTwoState, realTruthOffGridState,
    Fin.ext_iff]

theorem realTruthMinusTwo_has_offGrid_betterResponse :
    IsBetterResponse realWitnessPeaks realWitnessFollowers
      realTruthMinusTwoState (2 : Fin 3) (-19 / 10) := by
  constructor
  · rw [realTruthOffGridState_eq_update, realTruthMinusTwo_outcome,
      realTruthOffGrid_outcome]
    norm_num
  · intro hsp
    rw [realTruthOffGridState_eq_update, realTruthMinusTwo_outcome,
      realTruthOffGrid_outcome] at hsp
    norm_num [SPPrefers, realWitnessPeaks] at hsp

theorem realTruthMinusTwo_gridPNE_not_realPNE :
    ¬ IsPNE realWitnessPeaks realWitnessFollowers realTruthMinusTwoState := by
  intro h
  exact h (2 : Fin 3) (-19 / 10)
    realTruthMinusTwo_has_offGrid_betterResponse

noncomputable def realWitnessFollowersMisreport : Fin 3 → ℝ
  | 0 => 3
  | 1 => -2
  | 2 => 1

noncomputable def realMisreportOneState : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 4

noncomputable def realMisreportOffGridState : Fin 3 → ℝ
  | 0 => 0
  | 1 => 11 / 10
  | 2 => 4

private theorem realMisreportOne_cum_neg2 :
    Math.cumWeight (allPos realMisreportOneState realWitnessFollowersMisreport)
      (fun _ => 1) (-2) = 1 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realMisreportOneState realWitnessFollowersMisreport a ≤ -2)
        = ({Sum.inr (1 : Fin 3)} : Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realMisreportOneState]; try norm_num)
    | inr i =>
        fin_cases i <;>
          (simp [allPos, realWitnessFollowersMisreport]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realMisreportOne_cum_zero :
    Math.cumWeight (allPos realMisreportOneState realWitnessFollowersMisreport)
      (fun _ => 1) 0 = 2 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realMisreportOneState realWitnessFollowersMisreport a ≤ 0)
        = ({Sum.inl (0 : Fin 3), Sum.inr (1 : Fin 3)} :
          Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realMisreportOneState]; try norm_num)
    | inr i =>
        fin_cases i <;>
          (simp [allPos, realWitnessFollowersMisreport]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realMisreportOne_cum_one :
    Math.cumWeight (allPos realMisreportOneState realWitnessFollowersMisreport)
      (fun _ => 1) 1 = 4 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realMisreportOneState realWitnessFollowersMisreport a ≤ 1)
        = ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3),
            Sum.inr (1 : Fin 3), Sum.inr (2 : Fin 3)} :
          Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realMisreportOneState]; try norm_num)
    | inr i =>
        fin_cases i <;>
          (simp [allPos, realWitnessFollowersMisreport]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realMisreportOne_socialMedian :
    socialMedian realMisreportOneState realWitnessFollowersMisreport = 1 := by
  classical
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr
      ⟨Sum.inl (1 : Fin 3), Finset.mem_univ _, by
        simp [allPos, realMisreportOneState]⟩
  · rw [realMisreportOne_cum_one]
    norm_num [Math.totalWeight]
  · intro z hz hlt
    rcases Finset.mem_image.mp hz with ⟨a, -, rfl⟩
    cases a with
    | inl i =>
        fin_cases i
        · change 2 *
            Math.cumWeight
              (allPos realMisreportOneState realWitnessFollowersMisreport)
              (fun _ => 1) 0
              < Math.totalWeight (fun _ : Fin 3 ⊕ Fin 3 => 1)
          rw [realMisreportOne_cum_zero]
          norm_num [Math.totalWeight]
        · norm_num [allPos, realMisreportOneState] at hlt
        · norm_num [allPos, realMisreportOneState] at hlt
    | inr i =>
        fin_cases i
        · norm_num [allPos, realWitnessFollowersMisreport] at hlt
        · change 2 *
            Math.cumWeight
              (allPos realMisreportOneState realWitnessFollowersMisreport)
              (fun _ => 1) (-2)
              < Math.totalWeight (fun _ : Fin 3 ⊕ Fin 3 => 1)
          rw [realMisreportOne_cum_neg2]
          norm_num [Math.totalWeight]
        · norm_num [allPos, realWitnessFollowersMisreport] at hlt

private theorem realMisreportOne_outcome :
    outcome realMisreportOneState realWitnessFollowersMisreport = 1 := by
  have hk : realMisreportOneState (1 : Fin 3)
      = socialMedian realMisreportOneState realWitnessFollowersMisreport := by
    rw [realMisreportOne_socialMedian]
    norm_num [realMisreportOneState]
  rw [outcome_eq_socialMedian_of_report_at hk, realMisreportOne_socialMedian]

private theorem realMisreportOffGrid_cum_neg2 :
    Math.cumWeight (allPos realMisreportOffGridState realWitnessFollowersMisreport)
      (fun _ => 1) (-2) = 1 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realMisreportOffGridState realWitnessFollowersMisreport a ≤ -2)
        = ({Sum.inr (1 : Fin 3)} : Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realMisreportOffGridState]; try norm_num)
    | inr i =>
        fin_cases i <;>
          (simp [allPos, realWitnessFollowersMisreport]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realMisreportOffGrid_cum_zero :
    Math.cumWeight (allPos realMisreportOffGridState realWitnessFollowersMisreport)
      (fun _ => 1) 0 = 2 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realMisreportOffGridState realWitnessFollowersMisreport a ≤ 0)
        = ({Sum.inl (0 : Fin 3), Sum.inr (1 : Fin 3)} :
          Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realMisreportOffGridState]; try norm_num)
    | inr i =>
        fin_cases i <;>
          (simp [allPos, realWitnessFollowersMisreport]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realMisreportOffGrid_cum_one :
    Math.cumWeight (allPos realMisreportOffGridState realWitnessFollowersMisreport)
      (fun _ => 1) 1 = 3 := by
  classical
  have hfilter :
      (Finset.univ.filter fun a : Fin 3 ⊕ Fin 3 =>
          allPos realMisreportOffGridState realWitnessFollowersMisreport a ≤ 1)
        = ({Sum.inl (0 : Fin 3), Sum.inr (1 : Fin 3),
            Sum.inr (2 : Fin 3)} : Finset (Fin 3 ⊕ Fin 3)) := by
    ext a
    cases a with
    | inl i =>
        fin_cases i <;> (simp [allPos, realMisreportOffGridState]; try norm_num)
    | inr i =>
        fin_cases i <;>
          (simp [allPos, realWitnessFollowersMisreport]; try norm_num)
  rw [Math.cumWeight]
  simp [hfilter]

private theorem realMisreportOffGrid_socialMedian :
    socialMedian realMisreportOffGridState realWitnessFollowersMisreport = 1 := by
  classical
  unfold socialMedian
  refine Math.weightedMedian_eq_of_candidate_of_forall_lt ?_ ?_ ?_
  · exact Finset.mem_image.mpr
      ⟨Sum.inr (2 : Fin 3), Finset.mem_univ _, by
        simp [allPos, realWitnessFollowersMisreport]⟩
  · rw [realMisreportOffGrid_cum_one]
    norm_num [Math.totalWeight]
  · intro z hz hlt
    rcases Finset.mem_image.mp hz with ⟨a, -, rfl⟩
    cases a with
    | inl i =>
        fin_cases i
        · change 2 *
            Math.cumWeight
              (allPos realMisreportOffGridState realWitnessFollowersMisreport)
              (fun _ => 1) 0
              < Math.totalWeight (fun _ : Fin 3 ⊕ Fin 3 => 1)
          rw [realMisreportOffGrid_cum_zero]
          norm_num [Math.totalWeight]
        · norm_num [allPos, realMisreportOffGridState] at hlt
        · norm_num [allPos, realMisreportOffGridState] at hlt
    | inr i =>
        fin_cases i
        · norm_num [allPos, realWitnessFollowersMisreport] at hlt
        · change 2 *
            Math.cumWeight
              (allPos realMisreportOffGridState realWitnessFollowersMisreport)
              (fun _ => 1) (-2)
              < Math.totalWeight (fun _ : Fin 3 ⊕ Fin 3 => 1)
          rw [realMisreportOffGrid_cum_neg2]
          norm_num [Math.totalWeight]
        · norm_num [allPos, realWitnessFollowersMisreport] at hlt

private theorem realMisreportOffGrid_outcome :
    outcome realMisreportOffGridState realWitnessFollowersMisreport = 11 / 10 := by
  unfold outcome winner
  rw [realMisreportOffGrid_socialMedian]
  have hdel : delegate realMisreportOffGridState 1 = (1 : Fin 3) := by
    refine delegate_eq_of_forall_lt (s := realMisreportOffGridState) ?_
    intro j hj
    fin_cases j <;> simp [realMisreportOffGridState] at hj ⊢ <;> norm_num
  simp [hdel, realMisreportOffGridState]

private theorem realMisreportOffGridState_eq_update :
    Function.update realMisreportOneState (1 : Fin 3) (11 / 10)
      = realMisreportOffGridState := by
  funext j
  fin_cases j <;> simp [realMisreportOneState, realMisreportOffGridState,
    Fin.ext_iff]

theorem realMisreportOne_has_offGrid_betterResponse :
    IsBetterResponse realWitnessPeaks realWitnessFollowersMisreport
      realMisreportOneState (1 : Fin 3) (11 / 10) := by
  constructor
  · rw [realMisreportOffGridState_eq_update, realMisreportOne_outcome,
      realMisreportOffGrid_outcome]
    norm_num
  · intro hsp
    rw [realMisreportOffGridState_eq_update, realMisreportOne_outcome,
      realMisreportOffGrid_outcome] at hsp
    norm_num [SPPrefers, realWitnessPeaks] at hsp

theorem realMisreportOne_gridPNE_not_realPNE :
    ¬ IsPNE realWitnessPeaks realWitnessFollowersMisreport
      realMisreportOneState := by
  intro h
  exact h (1 : Fin 3) (11 / 10)
    realMisreportOne_has_offGrid_betterResponse

end ProxyVoting

end GameTheory
