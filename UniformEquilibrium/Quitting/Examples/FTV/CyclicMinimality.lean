/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.Models.Quitting.Game

/-!
# Minimality and normalized rigidity of the FTV quitting cycle

This file isolates the finite algebra of the FTV cyclic quitting class's
minimality and rigidity argument.  Its scope is the uniformly absorbing
cyclic quitting class; it makes no claim about arbitrary public
controllers.

The first layer below is the exact algebra consumed after the exposed-face
argument has shown that each live phase has one active solo-quitter role and
that all three roles occur.  Those hypotheses are explicit theorem
arguments, not fields of a certificate carrying the desired conclusion.
The later layer connects them to the concrete `(Q1)--(Q5)` packet.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace FTVCyclicMinimality

/-- The three FTV players. -/
abbrev Player := Fin 3

/-- The three solo-quitter payoff vectors `A`, `B'`, and `C`. -/
def soloReward : Player → Payoff Player :=
  ![![1, 3, 0], ![0, 1, 3], ![3, 0, 1]]

/-- The named initial continuation promise. -/
def namedTarget : Payoff Player := ![1, 2, 1]

/-- The cyclic successor on three normalized phases. -/
def nextThree : Fin 3 → Fin 3 := ![1, 2, 0]

@[simp] theorem nextThree_zero : nextThree 0 = 1 := rfl

@[simp] theorem nextThree_one : nextThree 1 = 2 := rfl

@[simp] theorem nextThree_two : nextThree 2 = 0 := rfl

@[simp] theorem soloReward_self (who : Player) : soloReward who who = 1 := by
  fin_cases who <;> rfl

/-- Three distinct solo roles cannot be supplied by fewer than three phases.
This is the cardinality step in the minimality proof, after exposure has
produced a surjective active-role map. -/
theorem period_ge_three_of_surjective_activeRole {K : ℕ} [NeZero K]
    (activeRole : Fin K → Player) (hcover : Function.Surjective activeRole) :
    3 ≤ K := by
  simpa using Fintype.card_le_of_surjective activeRole hcover

/-- The explicit reduction packet used by the three-phase rigidity algebra.

* `role` records the unique solo-quitter role in each phase;
* `hrole` says all three roles occur (hence, at three phases, exactly once);
* `hpromise` is `(Q1)` after exposure has killed every non-solo terminal row;
* `hactive` is the active player's equality clause of `(Q4)`.

No probability, role order, or continuation promise asserted in the
conclusion occurs among the hypotheses. -/
theorem three_phase_normalized_rigidity
    (role : Fin 3 → Player) (hrole : Function.Bijective role)
    (quitProb : Fin 3 → ℝ)
    (hquitProb : ∀ c, 0 < quitProb c ∧ quitProb c < 1)
    (promise : Fin 3 → Payoff Player)
    (hinitial : promise 0 = namedTarget)
    (hpromise : ∀ c,
      promise c = quitProb c • soloReward (role c) +
        (1 - quitProb c) • promise (nextThree c))
    (hactive : ∀ c,
      promise c (role c) = 1 ∧ promise (nextThree c) (role c) = 1) :
    role = ![0, 1, 2] ∧
      quitProb = ![(1 / 2 : ℝ), 1 / 2, 1 / 2] ∧
      promise = ![![1, 2, 1], ![1, 1, 2], ![2, 1, 1]] := by
  have hpair : role 0 = 0 ∧ role 1 = 1 := by
    have h0active := (hactive 0).1
    have h1active := (hactive 1).1
    have hstep0 := congrFun (hpromise 0) (role 1)
    have hinj01 : role 0 ≠ role 1 := by
      intro h
      exact (show (0 : Fin 3) ≠ 1 by decide) (hrole.1 h)
    rw [hinitial] at h0active hstep0
    generalize h0 : role 0 = r0
    generalize h1 : role 1 = r1
    fin_cases r0 <;> fin_cases r1
    · exact (hinj01 (h0.trans h1.symm)).elim
    · simp [h0, h1, namedTarget, soloReward, nextThree] at h0active h1active hstep0
      have hx := hquitProb 0
      exact ⟨by simp, by simp⟩
    · simp [h0, h1, namedTarget, soloReward, nextThree] at h0active h1active hstep0
      have hx := hquitProb 0
      nlinarith
    · simp [h0, namedTarget] at h0active
    · exact (hinj01 (h0.trans h1.symm)).elim
    · simp [h0, namedTarget] at h0active
    · simp [h0, h1, namedTarget, soloReward, nextThree] at h0active h1active hstep0
      have hx := hquitProb 0
      nlinarith
    · simp [h0, h1, namedTarget, soloReward, nextThree] at h0active h1active hstep0
      have hx := hquitProb 0
      nlinarith
    · exact (hinj01 (h0.trans h1.symm)).elim
  have hrole0 : role 0 = 0 := hpair.1
  have hrole1 : role 1 = 1 := hpair.2
  have hrole2 : role 2 = 2 := by
    have h20 : role 2 ≠ role 0 := by
      intro h
      exact (show (2 : Fin 3) ≠ 0 by decide) (hrole.1 h)
    have h21 : role 2 ≠ role 1 := by
      intro h
      exact (show (2 : Fin 3) ≠ 1 by decide) (hrole.1 h)
    generalize h2 : role 2 = r2
    fin_cases r2
    · exact (h20 (h2.trans hrole0.symm)).elim
    · exact (h21 (h2.trans hrole1.symm)).elim
    · simp
  have hprob0 : quitProb 0 = 1 / 2 := by
    have hstep0 := congrFun (hpromise 0) 1
    have hnextActive := (hactive 1).1
    rw [hinitial, hrole0] at hstep0
    rw [hrole1] at hnextActive
    simp [namedTarget, soloReward, nextThree, hnextActive] at hstep0
    linarith
  have hpromise1 : promise 1 = ![1, 1, 2] := by
    have hstep0 := hpromise 0
    rw [hinitial, hrole0, hprob0] at hstep0
    funext who
    fin_cases who
    · change promise 1 0 = 1
      have h := congrFun hstep0 (0 : Player)
      change (1 : ℝ) = (1 / 2 : ℝ) * 1 +
        (1 - 1 / 2) * promise 1 0 at h
      norm_num at h
      linarith
    · change promise 1 1 = 1
      have h := congrFun hstep0 (1 : Player)
      change (2 : ℝ) = (1 / 2 : ℝ) * 3 +
        (1 - 1 / 2) * promise 1 1 at h
      norm_num at h
      linarith
    · change promise 1 2 = 2
      have h := congrFun hstep0 (2 : Player)
      change (1 : ℝ) = (1 / 2 : ℝ) * 0 +
        (1 - 1 / 2) * promise 1 2 at h
      norm_num at h
      linarith
  have hprob1 : quitProb 1 = 1 / 2 := by
    have hstep1 := congrFun (hpromise 1) 2
    have hnextActive := (hactive 2).1
    rw [hpromise1, hrole1] at hstep1
    rw [hrole2] at hnextActive
    simp [soloReward, nextThree, hnextActive] at hstep1
    linarith
  have hpromise2 : promise 2 = ![2, 1, 1] := by
    have hstep1 := hpromise 1
    rw [hpromise1, hrole1, hprob1] at hstep1
    funext who
    fin_cases who
    · change promise 2 0 = 2
      have h := congrFun hstep1 (0 : Player)
      change (1 : ℝ) = (1 / 2 : ℝ) * 0 +
        (1 - 1 / 2) * promise 2 0 at h
      norm_num at h
      linarith
    · change promise 2 1 = 1
      have h := congrFun hstep1 (1 : Player)
      change (1 : ℝ) = (1 / 2 : ℝ) * 1 +
        (1 - 1 / 2) * promise 2 1 at h
      norm_num at h
      linarith
    · change promise 2 2 = 1
      have h := congrFun hstep1 (2 : Player)
      change (2 : ℝ) = (1 / 2 : ℝ) * 3 +
        (1 - 1 / 2) * promise 2 2 at h
      norm_num at h
      linarith
  have hprob2 : quitProb 2 = 1 / 2 := by
    have hstep2 := congrFun (hpromise 2) 1
    rw [hpromise2, hrole2, nextThree_two, hinitial] at hstep2
    simp [soloReward, namedTarget] at hstep2
    linarith
  refine ⟨?_, ?_, ?_⟩
  · funext c
    fin_cases c <;> assumption
  · funext c
    fin_cases c <;> assumption
  · funext c
    fin_cases c
    · exact hinitial
    · exact hpromise1
    · exact hpromise2

/-! ## The concrete finite `(Q1)--(Q5)` packet -/

/-- A pure quit/continue profile (`true` means quit). -/
abbrev JointQuit := Player → Bool

/-- The all-continue profile. -/
def allContinue : JointQuit := ![false, false, false]

/-- The three solo-quitter profiles. -/
def soloProfile : Player → JointQuit :=
  ![![true, false, false], ![false, true, false], ![false, false, true]]

/-- The complete FTV terminal table, with zero assigned to all-continue.
The latter value is ignored by terminal sums and only simplifies total table
statements. -/
def terminalReward (a : JointQuit) : Payoff Player :=
  match a 0, a 1, a 2 with
  | false, false, false => ![0, 0, 0]
  | true, false, false => ![1, 3, 0]
  | false, true, false => ![0, 1, 3]
  | false, false, true => ![3, 0, 1]
  | true, true, false => ![1, 0, 1]
  | true, false, true => ![0, 1, 1]
  | false, true, true => ![1, 1, 0]
  | true, true, true => ![0, 0, 0]

/-- Sum of the three payoff coordinates, the functional used to expose the
terminal-reward bound below. -/
def coordinateSum (u : Payoff Player) : ℝ := u 0 + u 1 + u 2

/-- A pure terminal row has exactly one quitter. -/
def IsSoloProfile (a : JointQuit) : Prop :=
  (a 0 = true ∧ a 1 = false ∧ a 2 = false) ∨
  (a 0 = false ∧ a 1 = true ∧ a 2 = false) ∨
  (a 0 = false ∧ a 1 = false ∧ a 2 = true)

@[simp] theorem terminalReward_soloProfile (who : Player) :
    terminalReward (soloProfile who) = soloReward who := by
  fin_cases who <;> rfl

@[simp] theorem coordinateSum_namedTarget : coordinateSum namedTarget = 4 := by
  norm_num [coordinateSum, namedTarget, Matrix.cons_val_two]

theorem coordinateSum_terminalReward_le_four (a : JointQuit) :
    coordinateSum (terminalReward a) ≤ 4 := by
  cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;>
    norm_num [coordinateSum, terminalReward, Matrix.cons_val_two, h0, h1, h2]

/-- Exact exposed-face classification: equality in the coordinate-sum bound
occurs precisely at one of the three solo-quitter rows. -/
theorem coordinateSum_terminalReward_eq_four_iff (a : JointQuit) :
    coordinateSum (terminalReward a) = 4 ↔ IsSoloProfile a := by
  cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2
  all_goals
    norm_num [coordinateSum, terminalReward, IsSoloProfile,
      Matrix.cons_val_two, h0, h1, h2]

theorem isSoloProfile_iff_exists_eq_soloProfile (a : JointQuit) :
    IsSoloProfile a ↔ ∃ who, a = soloProfile who := by
  constructor
  · rintro (h | h | h)
    · exact ⟨0, by funext who; fin_cases who <;> simp [soloProfile, h.1, h.2.1, h.2.2]⟩
    · exact ⟨1, by funext who; fin_cases who <;> simp [soloProfile, h.1, h.2.1, h.2.2]⟩
    · exact ⟨2, by funext who; fin_cases who <;> simp [soloProfile, h.1, h.2.1, h.2.2]⟩
  · rintro ⟨who, rfl⟩
    fin_cases who <;> simp [IsSoloProfile, soloProfile]

/-- Equivalence used only to expand finite sums over the eight pure rows. -/
def jointQuitEquiv : JointQuit ≃ Bool × Bool × Bool where
  toFun a := (a 0, a 1, a 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv a := by
    funext who
    fin_cases who <;> simp
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    rfl

/-- Fubini expansion of an eight-row finite sum. -/
theorem sum_jointQuit (f : JointQuit → ℝ) :
    (∑ a : JointQuit, f a) =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, f ![a, b, c] := by
  calc
    (∑ a : JointQuit, f a) =
        ∑ p : Bool × Bool × Bool, f (jointQuitEquiv.symm p) := by
          exact Fintype.sum_equiv jointQuitEquiv f
            (fun p => f (jointQuitEquiv.symm p))
            (fun a => congrArg f (jointQuitEquiv.left_inv a).symm)
    _ = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, f ![a, b, c] := by
      simp [Fintype.sum_prod_type, jointQuitEquiv]

/-- Independent probability of a pure row at one phase. -/
def profileProbability (x : Player → ℝ) (a : JointQuit) : ℝ :=
  ∏ who : Player, if a who then x who else 1 - x who

/-- Probability that everybody continues at one phase. -/
def survivalProbability (x : Player → ℝ) : ℝ :=
  profileProbability x allContinue

/-- The seven terminal rows. -/
def terminalProfiles : Finset JointQuit := Finset.univ.erase allContinue

@[simp] theorem profileProbability_allContinue (x : Player → ℝ) :
    profileProbability x allContinue = survivalProbability x :=
  rfl

theorem sum_profileProbability_eq_one (x : Player → ℝ) :
    (∑ a : JointQuit, profileProbability x a) = 1 := by
  rw [sum_jointQuit]
  simp only [Fintype.sum_bool, profileProbability, Fin.prod_univ_three]
  simp
  ring

theorem sum_terminal_profileProbability (x : Player → ℝ) :
    (∑ a ∈ terminalProfiles, profileProbability x a) =
      1 - survivalProbability x := by
  have htotal := sum_profileProbability_eq_one x
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ allContinue)] at htotal
  rw [terminalProfiles, survivalProbability]
  linarith

theorem profileProbability_nonneg {x : Player → ℝ}
    (hx : ∀ who, 0 ≤ x who ∧ x who ≤ 1) (a : JointQuit) :
    0 ≤ profileProbability x a := by
  unfold profileProbability
  exact Finset.prod_nonneg fun who _ => by
    by_cases h : a who
    · simp [h, (hx who).1]
    · simp [h, sub_nonneg.mpr (hx who).2]

theorem survivalProbability_nonneg {x : Player → ℝ}
    (hx : ∀ who, 0 ≤ x who ∧ x who ≤ 1) :
    0 ≤ survivalProbability x :=
  profileProbability_nonneg hx allContinue

/-- Terminal expectation in `(Q1)`. -/
def terminalExpectation (x : Player → ℝ) : Payoff Player :=
  ∑ a ∈ terminalProfiles, profileProbability x a • terminalReward a

/-- The nonnegative loss in the exposing functional relative to its maximum
four. -/
def exposedLoss (x : Player → ℝ) : ℝ :=
  ∑ a ∈ terminalProfiles,
    profileProbability x a * (4 - coordinateSum (terminalReward a))

theorem exposedLoss_nonneg {x : Player → ℝ}
    (hx : ∀ who, 0 ≤ x who ∧ x who ≤ 1) : 0 ≤ exposedLoss x := by
  unfold exposedLoss
  exact Finset.sum_nonneg fun a _ => mul_nonneg
    (profileProbability_nonneg hx a)
    (sub_nonneg.mpr (coordinateSum_terminalReward_le_four a))

/-- Cyclic successor on `K` phases. -/
def nextPhase (K : ℕ) [NeZero K] (c : Fin K) : Fin K :=
  Fin.ofNat K (c + 1)

theorem nextPhase_finOfNat (K : ℕ) [NeZero K] (n : ℕ) :
    nextPhase K (Fin.ofNat K n) = Fin.ofNat K (n + 1) := by
  apply Fin.ext
  simp [nextPhase, Fin.ofNat, Nat.add_mod]

/-- `(Q2)` expanded from the concrete FTV table. -/
def quitBranchValue (x : Player → ℝ) : Payoff Player :=
  ![1 - x 2, 1 - x 0, 1 - x 1]

/-- `(Q3)` expanded from the concrete FTV table.  `next` is the promise at
the cyclic successor phase. -/
def continueBranchValue (x : Player → ℝ) (next : Payoff Player) :
    Payoff Player :=
  ![(1 - x 1) * (1 - x 2) * next 0 +
      3 * (1 - x 1) * x 2 + x 1 * x 2,
    (1 - x 0) * (1 - x 2) * next 1 +
      3 * x 0 * (1 - x 2) + x 0 * x 2,
    (1 - x 0) * (1 - x 1) * next 2 +
      3 * (1 - x 0) * x 1 + x 0 * x 1]

/-- Exact supportwise complementarity `(Q4)`. -/
def IsExactlyComplementary (prob continueValue quitValue : ℝ) : Prop :=
  (prob = 0 ∧ quitValue ≤ continueValue) ∨
  (0 < prob ∧ prob < 1 ∧ continueValue = quitValue) ∨
  (prob = 1 ∧ continueValue ≤ quitValue)

/-- The finite data and the exact `(Q1)--(Q5)` assumptions for the cyclic
quitting minimality argument.

`live` is the live-phase restriction.  `q5` is recorded separately even
though, in this live finite cyclic class, it also follows from the
phasewise strict survival bound.  No unique-role or role-coverage
fact is included in this structure. -/
structure ExactCyclicPacket (K : ℕ) [NeZero K] where
  quitProb : Fin K → Player → ℝ
  promise : Fin K → Payoff Player
  probability_mem : ∀ c who,
    0 ≤ quitProb c who ∧ quitProb c who ≤ 1
  q1 : ∀ c,
    promise c = survivalProbability (quitProb c) • promise (nextPhase K c) +
      terminalExpectation (quitProb c)
  q4 : ∀ c who,
    IsExactlyComplementary (quitProb c who)
      (continueBranchValue (quitProb c) (promise (nextPhase K c)) who)
      (quitBranchValue (quitProb c) who)
  q5 : (∏ c : Fin K, survivalProbability (quitProb c)) < 1
  live : ∀ c,
    0 < survivalProbability (quitProb c) ∧
      survivalProbability (quitProb c) < 1
  initial : promise 0 = namedTarget

namespace ExactCyclicPacket

variable {K : ℕ} [NeZero K] (A : ExactCyclicPacket K)

theorem coordinateSum_smul (r : ℝ) (u : Payoff Player) :
    coordinateSum (r • u) = r * coordinateSum u := by
  simp [coordinateSum]
  ring

theorem coordinateSum_add (u v : Payoff Player) :
    coordinateSum (u + v) = coordinateSum u + coordinateSum v := by
  simp [coordinateSum]
  ring

theorem coordinateSum_terminalExpectation (x : Player → ℝ) :
    coordinateSum (terminalExpectation x) =
      ∑ a ∈ terminalProfiles,
        profileProbability x a * coordinateSum (terminalReward a) := by
  simp only [terminalExpectation, coordinateSum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem exposedLoss_eq (x : Player → ℝ) :
    exposedLoss x = 4 * (1 - survivalProbability x) -
      coordinateSum (terminalExpectation x) := by
  rw [coordinateSum_terminalExpectation, exposedLoss]
  have hmass := sum_terminal_profileProbability x
  calc
    (∑ a ∈ terminalProfiles,
        profileProbability x a * (4 - coordinateSum (terminalReward a))) =
        (∑ a ∈ terminalProfiles, 4 * profileProbability x a) -
          ∑ a ∈ terminalProfiles,
            profileProbability x a * coordinateSum (terminalReward a) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro a ha
              ring
    _ = 4 * (1 - survivalProbability x) -
          ∑ a ∈ terminalProfiles,
            profileProbability x a * coordinateSum (terminalReward a) := by
              rw [← Finset.mul_sum, hmass]

/-- Exposed-coordinate deficit from the maximum value four. -/
def deficit (c : Fin K) : ℝ := 4 - coordinateSum (A.promise c)

/-- `(Q1)` rewritten as a nonnegative deficit recursion. -/
theorem deficit_q1 (c : Fin K) :
    A.deficit c = survivalProbability (A.quitProb c) *
        A.deficit (nextPhase K c) + exposedLoss (A.quitProb c) := by
  have hq := congrArg coordinateSum (A.q1 c)
  rw [coordinateSum_add,
    coordinateSum_smul] at hq
  have hloss := exposedLoss_eq (A.quitProb c)
  unfold deficit
  rw [hloss]
  nlinarith

/-- Every continuation promise lies weakly below the exposed hyperplane.
The proof is the finite cyclic minimum argument for the nonnegative deficit
recursion. -/
theorem deficit_nonneg (c : Fin K) : 0 ≤ A.deficit c := by
  obtain ⟨m, hm_univ, hm⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin K)) A.deficit Finset.univ_nonempty
  have hrec := A.deficit_q1 m
  have hnext : A.deficit m ≤ A.deficit (nextPhase K m) :=
    hm _ (Finset.mem_univ _)
  have hloss : 0 ≤ exposedLoss (A.quitProb m) :=
    exposedLoss_nonneg (A.probability_mem m)
  have hs := A.live m
  have hm0 : 0 ≤ A.deficit m := by
    nlinarith
  exact hm0.trans (hm c (Finset.mem_univ c))

@[simp] theorem deficit_zero : A.deficit 0 = 0 := by
  simp [deficit, A.initial]

theorem deficit_next_and_loss_eq_zero {c : Fin K} (hc : A.deficit c = 0) :
    A.deficit (nextPhase K c) = 0 ∧ exposedLoss (A.quitProb c) = 0 := by
  have hrec := A.deficit_q1 c
  have hnext := A.deficit_nonneg (nextPhase K c)
  have hloss : 0 ≤ exposedLoss (A.quitProb c) :=
    exposedLoss_nonneg (A.probability_mem c)
  have hs := (A.live c).1
  constructor <;> nlinarith

/-- Equality in the exposing functional propagates around the entire cyclic
word from the named phase. -/
theorem deficit_eq_zero (c : Fin K) : A.deficit c = 0 := by
  have hseq : ∀ n : ℕ, A.deficit (Fin.ofNat K n) = 0 := by
    intro n
    induction n with
    | zero => simpa only [Fin.ofNat_zero] using A.deficit_zero
    | succ n ih =>
        rw [← nextPhase_finOfNat]
        exact (A.deficit_next_and_loss_eq_zero ih).1
  have hc : Fin.ofNat K c.val = c := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt c.isLt]
  rw [← hc]
  exact hseq c.val

theorem exposedLoss_eq_zero (c : Fin K) :
    exposedLoss (A.quitProb c) = 0 :=
  (A.deficit_next_and_loss_eq_zero (A.deficit_eq_zero c)).2

/-- Any terminal row assigned positive probability at any phase is a
solo-quitter row. -/
theorem isSoloProfile_of_profileProbability_pos (c : Fin K) (a : JointQuit)
    (ha : a ∈ terminalProfiles) (hprob : 0 < profileProbability (A.quitProb c) a) :
    IsSoloProfile a := by
  have hgap : 0 ≤ 4 - coordinateSum (terminalReward a) :=
    sub_nonneg.mpr (coordinateSum_terminalReward_le_four a)
  have hterm_nonneg : ∀ b ∈ terminalProfiles,
      0 ≤ profileProbability (A.quitProb c) b *
        (4 - coordinateSum (terminalReward b)) := by
    intro b hb
    exact mul_nonneg (profileProbability_nonneg (A.probability_mem c) b)
      (sub_nonneg.mpr (coordinateSum_terminalReward_le_four b))
  have hle : profileProbability (A.quitProb c) a *
        (4 - coordinateSum (terminalReward a)) ≤
      exposedLoss (A.quitProb c) := by
    unfold exposedLoss
    exact Finset.single_le_sum hterm_nonneg ha
  rw [A.exposedLoss_eq_zero c] at hle
  have hsum : coordinateSum (terminalReward a) = 4 := by
    nlinarith
  exact (coordinateSum_terminalReward_eq_four_iff a).mp hsum

theorem survivalProbability_eq (c : Fin K) :
    survivalProbability (A.quitProb c) =
      (1 - A.quitProb c 0) * (1 - A.quitProb c 1) *
        (1 - A.quitProb c 2) := by
  simp [survivalProbability, profileProbability, allContinue,
    Fin.prod_univ_three]

theorem quitProb_lt_one (c : Fin K) (who : Player) :
    A.quitProb c who < 1 := by
  have hs := (A.live c).1
  rw [A.survivalProbability_eq c] at hs
  have h0 := A.probability_mem c 0
  have h1 := A.probability_mem c 1
  have h2 := A.probability_mem c 2
  have hy0 : 0 ≤ 1 - A.quitProb c 0 := sub_nonneg.mpr h0.2
  have hy1 : 0 ≤ 1 - A.quitProb c 1 := sub_nonneg.mpr h1.2
  have hy2 : 0 ≤ 1 - A.quitProb c 2 := sub_nonneg.mpr h2.2
  have hpairs : 0 < (1 - A.quitProb c 0) * (1 - A.quitProb c 1) := by
    rcases (mul_pos_iff.mp hs) with hpos | hneg
    · exact hpos.1
    · linarith
  have hy2pos : 0 < 1 - A.quitProb c 2 := by
    rcases (mul_pos_iff.mp hs) with hpos | hneg
    · exact hpos.2
    · linarith
  have hy0pos : 0 < 1 - A.quitProb c 0 := by
    rcases (mul_pos_iff.mp hpairs) with hpos | hneg
    · exact hpos.1
    · linarith
  have hy1pos : 0 < 1 - A.quitProb c 1 := by
    rcases (mul_pos_iff.mp hpairs) with hpos | hneg
    · exact hpos.2
    · linarith
  fin_cases who
  · simpa using hy0pos
  · simpa using hy1pos
  · simpa using hy2pos

theorem exists_activeRole (c : Fin K) : ∃ who, 0 < A.quitProb c who := by
  by_contra h
  push Not at h
  have h0 : A.quitProb c 0 = 0 := le_antisymm (h 0) (A.probability_mem c 0).1
  have h1 : A.quitProb c 1 = 0 := le_antisymm (h 1) (A.probability_mem c 1).1
  have h2 : A.quitProb c 2 = 0 := le_antisymm (h 2) (A.probability_mem c 2).1
  have hs := (A.live c).2
  rw [A.survivalProbability_eq c, h0, h1, h2] at hs
  norm_num at hs

theorem activeRole_unique (c : Fin K) {i j : Player}
    (hi : 0 < A.quitProb c i) (hj : 0 < A.quitProb c j) : i = j := by
  by_contra hij
  let a : JointQuit := fun k => decide (k = i ∨ k = j)
  have hfactor : ∀ k : Player,
      0 < if a k then A.quitProb c k else 1 - A.quitProb c k := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [a, hi]
    · by_cases hkj : k = j
      · subst k
        simp [a, hj]
      · simp [a, hki, hkj, A.quitProb_lt_one c k]
  have hp : 0 < profileProbability (A.quitProb c) a := by
    unfold profileProbability
    exact Finset.prod_pos fun k _ => hfactor k
  have hne : a ≠ allContinue := by
    intro h
    have hiTrue : a i = true := by simp [a]
    rw [h] at hiTrue
    fin_cases i <;> simp [allContinue] at hiTrue
  have hmem : a ∈ terminalProfiles := by
    simp [terminalProfiles, hne]
  have hsolo := A.isSoloProfile_of_profileProbability_pos c a hmem hp
  fin_cases i <;> fin_cases j <;>
    simp [a, IsSoloProfile] at hsolo hij

theorem existsUnique_activeRole (c : Fin K) :
    ∃! who, 0 < A.quitProb c who := by
  obtain ⟨who, hwho⟩ := A.exists_activeRole c
  exact ⟨who, hwho, fun j hj => A.activeRole_unique c hj hwho⟩

/-- Barycentric coordinate on the exposed solo-reward face. -/
def roleWeight (who : Player) (u : Payoff Player) : ℝ :=
  if who = 0 then (u 0 + 9 * u 1 - 3 * u 2) / 28
  else if who = 1 then (-3 * u 0 + u 1 + 9 * u 2) / 28
  else (9 * u 0 - 3 * u 1 + u 2) / 28

theorem roleWeight_add (who : Player) (u v : Payoff Player) :
    roleWeight who (u + v) = roleWeight who u + roleWeight who v := by
  fin_cases who <;> simp [roleWeight] <;> ring

theorem roleWeight_smul (who : Player) (r : ℝ) (u : Payoff Player) :
    roleWeight who (r • u) = r * roleWeight who u := by
  fin_cases who <;> simp [roleWeight] <;> ring

theorem roleWeight_finsetSum {α : Type} (who : Player) (s : Finset α)
    (f : α → Payoff Player) :
    roleWeight who (∑ a ∈ s, f a) = ∑ a ∈ s, roleWeight who (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [roleWeight]
  | @insert a s ha ih =>
      simp [ha, ih, roleWeight_add]

@[simp] theorem roleWeight_soloReward (who role : Player) :
    roleWeight who (soloReward role) = if role = who then 1 else 0 := by
  fin_cases who <;> fin_cases role <;>
    norm_num [roleWeight, soloReward, Matrix.cons_val_two]

theorem roleWeight_namedTarget_pos (who : Player) :
    0 < roleWeight who namedTarget := by
  fin_cases who <;>
    norm_num [roleWeight, namedTarget, Matrix.cons_val_two]

theorem roleWeight_terminalExpectation (who : Player) (x : Player → ℝ) :
    roleWeight who (terminalExpectation x) =
      ∑ a ∈ terminalProfiles,
        profileProbability x a * roleWeight who (terminalReward a) := by
  unfold terminalExpectation
  rw [roleWeight_finsetSum]
  apply Finset.sum_congr rfl
  intro a ha
  exact roleWeight_smul who (profileProbability x a) (terminalReward a)

/-- The unique active solo role in a live phase. -/
noncomputable def activeRole (c : Fin K) : Player :=
  (A.existsUnique_activeRole c).choose

theorem activeRole_pos (c : Fin K) : 0 < A.quitProb c (A.activeRole c) :=
  (A.existsUnique_activeRole c).choose_spec.1

theorem quitProb_eq_zero_of_ne_activeRole (c : Fin K) (who : Player)
    (hne : who ≠ A.activeRole c) : A.quitProb c who = 0 := by
  have hnonpos : A.quitProb c who ≤ 0 := by
    by_contra h
    have hpos : 0 < A.quitProb c who :=
      lt_of_not_ge h
    exact hne ((A.existsUnique_activeRole c).choose_spec.2 who hpos)
  exact le_antisymm hnonpos (A.probability_mem c who).1

theorem sum_terminal_eq_sum_all (x : Player → ℝ) (f : JointQuit → ℝ)
    (hf : f allContinue = 0) :
    (∑ a ∈ terminalProfiles, profileProbability x a * f a) =
      ∑ a : JointQuit, profileProbability x a * f a := by
  rw [terminalProfiles]
  calc
    (∑ a ∈ (Finset.univ : Finset JointQuit).erase allContinue,
        profileProbability x a * f a) =
        (∑ a ∈ (Finset.univ : Finset JointQuit).erase allContinue,
          profileProbability x a * f a) +
            profileProbability x allContinue * f allContinue := by simp [hf]
    _ = ∑ a : JointQuit, profileProbability x a * f a :=
      Finset.sum_erase_add _ _ (Finset.mem_univ allContinue)

theorem survivalProbability_singleRole (role : Player) (q : ℝ) :
    survivalProbability (fun who => if who = role then q else 0) = 1 - q := by
  fin_cases role <;>
    simp [survivalProbability, profileProbability, allContinue,
      Fin.prod_univ_three]

theorem terminalExpectation_singleRole (role : Player) (q : ℝ) :
    terminalExpectation (fun who => if who = role then q else 0) =
      q • soloReward role := by
  fin_cases role
  all_goals
    funext who
    fin_cases who
    all_goals
      simp only [terminalExpectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_terminal_eq_sum_all]
      · rw [sum_jointQuit]
        simp only [Fintype.sum_bool]
        simp [profileProbability, Fin.prod_univ_three, terminalReward, soloReward,
          Matrix.cons_val_two]
      · simp [terminalReward, allContinue]

/-- Once exposure has produced the unique active role, `(Q1)`'s terminal
expectation is exactly that role's solo reward times its quitting
probability. -/
theorem terminalExpectation_eq_activeRole (c : Fin K) :
    terminalExpectation (A.quitProb c) =
      A.quitProb c (A.activeRole c) • soloReward (A.activeRole c) := by
  generalize hr : A.activeRole c = role
  have hz : ∀ who, who ≠ role → A.quitProb c who = 0 := by
    intro who hne
    apply A.quitProb_eq_zero_of_ne_activeRole c who
    simpa [hr] using hne
  fin_cases role
  · have hz1 := hz 1 (by decide)
    have hz2 := hz 2 (by decide)
    funext who
    fin_cases who
    all_goals
      simp only [terminalExpectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_terminal_eq_sum_all]
      · rw [sum_jointQuit]
        simp only [Fintype.sum_bool]
        simp [profileProbability, Fin.prod_univ_three, terminalReward, soloReward,
          hz1, hz2, Matrix.cons_val_two]
      · simp [terminalReward, allContinue]
  · have hz0 := hz 0 (by decide)
    have hz2 := hz 2 (by decide)
    funext who
    fin_cases who
    all_goals
      simp only [terminalExpectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_terminal_eq_sum_all]
      · rw [sum_jointQuit]
        simp only [Fintype.sum_bool]
        simp [profileProbability, Fin.prod_univ_three, terminalReward, soloReward,
          hz0, hz2, Matrix.cons_val_two]
      · simp [terminalReward, allContinue]
  · have hz0 := hz 0 (by decide)
    have hz1 := hz 1 (by decide)
    funext who
    fin_cases who
    all_goals
      simp only [terminalExpectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [sum_terminal_eq_sum_all]
      · rw [sum_jointQuit]
        simp only [Fintype.sum_bool]
        simp [profileProbability, Fin.prod_univ_three, terminalReward, soloReward,
          hz0, hz1, Matrix.cons_val_two]
      · simp [terminalReward, allContinue]

theorem survivalProbability_eq_one_sub_activeRole (c : Fin K) :
    survivalProbability (A.quitProb c) =
      1 - A.quitProb c (A.activeRole c) := by
  rw [A.survivalProbability_eq]
  generalize hr : A.activeRole c = role
  have hz : ∀ who, who ≠ role → A.quitProb c who = 0 := by
    intro who hne
    apply A.quitProb_eq_zero_of_ne_activeRole c who
    simpa [hr] using hne
  fin_cases role
  · rw [hz 1 (by decide), hz 2 (by decide)]
    simp
  · rw [hz 0 (by decide), hz 2 (by decide)]
    simp
  · rw [hz 0 (by decide), hz 1 (by decide)]
    simp

theorem quitBranchValue_activeRole (c : Fin K) :
    quitBranchValue (A.quitProb c) (A.activeRole c) = 1 := by
  generalize hr : A.activeRole c = role
  have hz : ∀ who, who ≠ role → A.quitProb c who = 0 := by
    intro who hne
    apply A.quitProb_eq_zero_of_ne_activeRole c who
    simpa [hr] using hne
  fin_cases role
  · simp [quitBranchValue, hz 2 (by decide)]
  · simp [quitBranchValue, hz 0 (by decide)]
  · simp [quitBranchValue, hz 1 (by decide), Matrix.cons_val_two]

theorem continueBranchValue_activeRole (c : Fin K) :
    continueBranchValue (A.quitProb c) (A.promise (nextPhase K c))
        (A.activeRole c) = A.promise (nextPhase K c) (A.activeRole c) := by
  generalize hr : A.activeRole c = role
  have hz : ∀ who, who ≠ role → A.quitProb c who = 0 := by
    intro who hne
    apply A.quitProb_eq_zero_of_ne_activeRole c who
    simpa [hr] using hne
  fin_cases role
  · simp [continueBranchValue, hz 1 (by decide), hz 2 (by decide)]
  · simp [continueBranchValue, hz 0 (by decide), hz 2 (by decide)]
  · simp [continueBranchValue, hz 0 (by decide), hz 1 (by decide),
      Matrix.cons_val_two]

theorem active_complementarity_eq (c : Fin K) :
    continueBranchValue (A.quitProb c) (A.promise (nextPhase K c))
        (A.activeRole c) = quitBranchValue (A.quitProb c) (A.activeRole c) := by
  have hq := A.q4 c (A.activeRole c)
  rcases hq with hzero | hinterior | hone
  · exact (ne_of_gt (A.activeRole_pos c) hzero.1).elim
  · exact hinterior.2.2
  · exact (ne_of_lt (A.quitProb_lt_one c (A.activeRole c)) hone.1).elim

theorem active_successor_promise_eq_one (c : Fin K) :
    A.promise (nextPhase K c) (A.activeRole c) = 1 := by
  rw [← A.continueBranchValue_activeRole c,
    A.active_complementarity_eq c,
    A.quitBranchValue_activeRole c]

/-- `(Q1)` after the exposed-face and unique-role reductions. -/
theorem q1_activeRole (c : Fin K) :
    A.promise c = A.quitProb c (A.activeRole c) • soloReward (A.activeRole c) +
      (1 - A.quitProb c (A.activeRole c)) • A.promise (nextPhase K c) := by
  rw [A.q1 c, A.survivalProbability_eq_one_sub_activeRole c,
    A.terminalExpectation_eq_activeRole c]
  ac_rfl

theorem active_current_promise_eq_one (c : Fin K) :
    A.promise c (A.activeRole c) = 1 := by
  have h := congrFun (A.q1_activeRole c) (A.activeRole c)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [soloReward_self, A.active_successor_promise_eq_one c] at h
  nlinarith

theorem roleWeight_terminalExpectation_eq_zero_of_quitProb_zero
    (c : Fin K) (who : Player) (hzero : A.quitProb c who = 0) :
    roleWeight who (terminalExpectation (A.quitProb c)) = 0 := by
  rw [roleWeight_terminalExpectation]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hpzero : profileProbability (A.quitProb c) a = 0
  · simp [hpzero]
  · have hppos : 0 < profileProbability (A.quitProb c) a :=
      lt_of_le_of_ne (profileProbability_nonneg (A.probability_mem c) a)
        (Ne.symm hpzero)
    have hsolo := A.isSoloProfile_of_profileProbability_pos c a ha hppos
    obtain ⟨role, rfl⟩ :=
      (isSoloProfile_iff_exists_eq_soloProfile _).mp hsolo
    have hrne : role ≠ who := by
      intro hr
      subst role
      have hp0 : profileProbability (A.quitProb c) (soloProfile who) = 0 := by
        fin_cases who
        · change A.quitProb c 0 = 0 at hzero
          simp [profileProbability, soloProfile, Fin.prod_univ_three, hzero,
            Matrix.cons_val_two]
        · change A.quitProb c 1 = 0 at hzero
          simp [profileProbability, soloProfile, Fin.prod_univ_three, hzero,
            Matrix.cons_val_two]
        · change A.quitProb c 2 = 0 at hzero
          simp [profileProbability, soloProfile, Fin.prod_univ_three, hzero,
            Matrix.cons_val_two]
      exact hpzero hp0
    simp [roleWeight_soloReward, hrne]

/-- Every one of the three solo roles occurs in some phase.  If a role never
occurred, its exposed-face barycentric coordinate would be multiplied by a
strict survival factor at every phase; maximizing its absolute value around
the finite cycle contradicts its positive named initial weight. -/
theorem activeRole_surjective : Function.Surjective A.activeRole := by
  intro who
  by_contra hmissing
  push Not at hmissing
  have hzero : ∀ c, A.quitProb c who = 0 := by
    intro c
    exact A.quitProb_eq_zero_of_ne_activeRole c who (Ne.symm (hmissing c))
  have hrec : ∀ c,
      roleWeight who (A.promise c) = survivalProbability (A.quitProb c) *
        roleWeight who (A.promise (nextPhase K c)) := by
    intro c
    have hq := congrArg (roleWeight who) (A.q1 c)
    rw [roleWeight_add, roleWeight_smul,
      A.roleWeight_terminalExpectation_eq_zero_of_quitProb_zero c who (hzero c)] at hq
    simpa using hq
  obtain ⟨m, hm_univ, hm⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin K))
    (fun c => |roleWeight who (A.promise c)|) Finset.univ_nonempty
  have hinitialPos : 0 < |roleWeight who (A.promise 0)| := by
    rw [A.initial, abs_of_pos (roleWeight_namedTarget_pos who)]
    exact roleWeight_namedTarget_pos who
  have hmpos : 0 < |roleWeight who (A.promise m)| :=
    hinitialPos.trans_le (hm 0 (Finset.mem_univ 0))
  have hnext := hm (nextPhase K m) (Finset.mem_univ _)
  have hsnonneg := survivalProbability_nonneg (A.probability_mem m)
  have habs := congrArg abs (hrec m)
  rw [abs_mul, abs_of_nonneg hsnonneg] at habs
  have hs := (A.live m).2
  nlinarith [abs_nonneg (roleWeight who (A.promise (nextPhase K m)))]

/-- Minimality in the exact stated cyclic domain: at least three phases
are needed. -/
theorem period_ge_three (A : ExactCyclicPacket K) : 3 ≤ K :=
  period_ge_three_of_surjective_activeRole (activeRole A) (activeRole_surjective A)

theorem nextPhase_three (c : Fin 3) : nextPhase 3 c = nextThree c := by
  fin_cases c <;> rfl

/-- The normalized quitting matrix in `(M2)`. -/
def standardQuitProb : Fin 3 → Player → ℝ :=
  fun c who => if who = c then 1 / 2 else 0

/-- The normalized promise word in `(M2)`. -/
def standardPromise : Fin 3 → Payoff Player :=
  ![![1, 2, 1], ![1, 1, 2], ![2, 1, 1]]

/-- The displayed `(M2)` packet genuinely satisfies the finite assumptions;
this prevents the minimality/rigidity interface from being vacuous. -/
def standardPacket : ExactCyclicPacket 3 where
  quitProb := standardQuitProb
  promise := standardPromise
  probability_mem := by
    intro c who
    simp [standardQuitProb]
    split <;> norm_num
  q1 := by
    intro c
    have hsurv := survivalProbability_singleRole c (1 / 2 : ℝ)
    have hterm := terminalExpectation_singleRole c (1 / 2 : ℝ)
    change standardPromise c =
      survivalProbability (fun who => if who = c then 1 / 2 else 0) •
          standardPromise (nextPhase 3 c) +
        terminalExpectation (fun who => if who = c then 1 / 2 else 0)
    rw [hsurv, hterm]
    fin_cases c
    all_goals
      funext who
      fin_cases who <;>
        simp [standardPromise, nextPhase_three, nextThree, soloReward] <;> norm_num
  q4 := by
    intro c who
    fin_cases c <;> fin_cases who <;>
      simp [IsExactlyComplementary, standardQuitProb, standardPromise,
        continueBranchValue, quitBranchValue, nextPhase_three, nextThree] <;> norm_num
  q5 := by
    rw [Fin.prod_univ_three]
    simp [standardQuitProb, survivalProbability, profileProbability,
      allContinue, Fin.prod_univ_three]; norm_num
  live := by
    intro c
    fin_cases c <;>
      simp [standardQuitProb, survivalProbability, profileProbability,
        allContinue, Fin.prod_univ_three] <;> norm_num
  initial := rfl

/-- Rigidity at the minimum, with the named phase-zero promise fixed.
The result is literal uniqueness at that named node.  The diagonal cyclic
player/phase relabeling maps this displayed packet back to itself; a
player relabeling alone or phase rotation alone is not asserted here. -/
theorem three_phase_rigidity (A : ExactCyclicPacket 3) :
    activeRole A = ![0, 1, 2] ∧
      A.quitProb = standardQuitProb ∧
      A.promise = standardPromise := by
  have hsurj : Function.Surjective (activeRole A) := activeRole_surjective A
  have hinj : Function.Injective (activeRole A) :=
    Finite.injective_iff_surjective.mpr hsurj
  have hbij : Function.Bijective (activeRole A) := ⟨hinj, hsurj⟩
  have hqpos : ∀ c, 0 < A.quitProb c (activeRole A c) ∧
      A.quitProb c (activeRole A c) < 1 := by
    intro c
    exact ⟨activeRole_pos A c, A.quitProb_lt_one c (activeRole A c)⟩
  have hq1 : ∀ c,
      A.promise c = A.quitProb c (activeRole A c) • soloReward (activeRole A c) +
        (1 - A.quitProb c (activeRole A c)) • A.promise (nextThree c) := by
    intro c
    simpa [nextPhase_three] using A.q1_activeRole c
  have hactive : ∀ c,
      A.promise c (activeRole A c) = 1 ∧
        A.promise (nextThree c) (activeRole A c) = 1 := by
    intro c
    refine ⟨A.active_current_promise_eq_one c, ?_⟩
    simpa [nextPhase_three] using A.active_successor_promise_eq_one c
  obtain ⟨hrole, hscalar, hpromise⟩ :=
    three_phase_normalized_rigidity (activeRole A) hbij
      (fun c => A.quitProb c (activeRole A c)) hqpos A.promise A.initial hq1 hactive
  refine ⟨hrole, ?_, hpromise⟩
  funext c who
  have hrpoint : activeRole A c = c := by
    rw [hrole]
    fin_cases c <;> rfl
  by_cases hwho : who = c
  · subst who
    have hs := congrFun hscalar c
    have hhalf : ![(1 / 2 : ℝ), 1 / 2, 1 / 2] c = 1 / 2 := by
      fin_cases c <;> rfl
    rw [hrpoint, hhalf] at hs
    simp [standardQuitProb]
    simpa [div_eq_mul_inv] using hs
  · have hr := congrFun hrole c
    have hz := A.quitProb_eq_zero_of_ne_activeRole c who
      (by simpa [hrpoint] using hwho)
    simp [standardQuitProb, hwho, hz]

end ExactCyclicPacket


end FTVCyclicMinimality
end GameTheory
