/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.InformationalGame
import Math.LinearProgramming.Certificates

/-!
# Informational-form implementation examples

Machine-checked examples from the incomplete-information section of
Monderer--Tennenholtz. The Figure 4 example is an ex-post equilibrium, but no
signal-blind action transfer can implement the displayed strategy profile by
undominated signal-contingent strategies.
-/

namespace GameTheory

namespace InformationalGame

variable {ι : Type}
variable {G : InformationalGame ι}

/-- Bonus transfer for conformance-based implementation. Player `i` receives
`B` exactly when their realized action conforms and some other player does not
conform. This abstracts the transfer pattern in the frugal-VCG theorem. -/
noncomputable def conformanceBonusTransfer
    (C : ∀ i, G.Act i → Prop) (B : ℝ) : G.ActionTransfer :=
  open Classical in
  fun a i =>
    if C i (a i) ∧ ∃ j : ι, j ≠ i ∧ ¬ C j (a j) then B else 0

theorem conformanceBonusTransfer_nonneg
    (C : ∀ i, G.Act i → Prop) {B : ℝ} (hB : 0 ≤ B) :
    ∀ a i, 0 ≤ G.conformanceBonusTransfer C B a i := by
  classical
  intro a i
  rw [conformanceBonusTransfer]
  split_ifs with h
  · exact hB
  · norm_num

private theorem conformance_other_update_iff
    [DecidableEq ι]
    (C : ∀ i, G.Act i → Prop) {i : ι} (a : G.ActionProfile)
    (ai : G.Act i) :
    (∃ j : ι, j ≠ i ∧ ¬ C j (Function.update a i ai j)) ↔
      ∃ j : ι, j ≠ i ∧ ¬ C j (a j) := by
  constructor
  · rintro ⟨j, hji, hj⟩
    exact ⟨j, hji, by simpa [Function.update_of_ne hji] using hj⟩
  · rintro ⟨j, hji, hj⟩
    exact ⟨j, hji, by simpa [Function.update_of_ne hji] using hj⟩

/-- Abstract conformance-bonus implementation lemma. If the target action is
best against conforming own deviations at every opponent action profile, and is
best against all deviations whenever all opponents conform, then a sufficiently
large conformance bonus makes the target profile ex-post dominant.

This isolates the game-independent part of the frugal-VCG proof: the VCG layer
only needs to supply the two base-game comparison hypotheses. -/
theorem conformanceBonusTransfer_isExPostDominantProfile
    [DecidableEq ι]
    (C : ∀ i, G.Act i → Prop)
    {σ : G.StrategyProfile} {M B : ℝ}
    (hσC : ∀ (θ : G.SignalProfile) i, C i (σ i (θ i)))
    (hbound : ∀ θ a i, |G.utility θ a i| ≤ M)
    (hbonus : 2 * M ≤ B)
    (hbest_conforming_deviation :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        C i a' →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i)
    (hbest_when_opponents_conform :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        (∀ j : ι, j ≠ i → C j (a j)) →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i) :
    G.IsExPostDominantProfileWithTransfer
      (G.conformanceBonusTransfer C B) σ := by
  classical
  intro i θ a a'
  by_cases ha' : C i a'
  · have hbase := hbest_conforming_deviation θ i a a' ha'
    have hpay_eq :
        G.conformanceBonusTransfer C B (Function.update a i (σ i (θ i))) i =
          G.conformanceBonusTransfer C B (Function.update a i a') i := by
      have hother :=
        conformance_other_update_iff (G := G) C (i := i) a (σ i (θ i))
      have hother' := conformance_other_update_iff (G := G) C (i := i) a a'
      simp [conformanceBonusTransfer, hσC θ i, ha', hother, hother']
    rw [subsidizedUtility, subsidizedUtility, hpay_eq]
    linarith
  · by_cases hother : ∃ j : ι, j ≠ i ∧ ¬ C j (a j)
    · have htarget_pay :
          G.conformanceBonusTransfer C B (Function.update a i (σ i (θ i))) i = B := by
        have hother_update :
            ∃ j : ι, j ≠ i ∧ ¬ C j (Function.update a i (σ i (θ i)) j) :=
          (conformance_other_update_iff (G := G) C (i := i) a (σ i (θ i))).mpr hother
        simp [conformanceBonusTransfer, hσC θ i, hother_update]
      have hdev_pay :
          G.conformanceBonusTransfer C B (Function.update a i a') i = 0 := by
        simp [conformanceBonusTransfer, ha']
      have htarget_lower :
          -M ≤ G.utility θ (Function.update a i (σ i (θ i))) i :=
        neg_le_of_abs_le (hbound θ (Function.update a i (σ i (θ i))) i)
      have hdev_upper :
          G.utility θ (Function.update a i a') i ≤ M :=
        le_of_abs_le (hbound θ (Function.update a i a') i)
      rw [subsidizedUtility, subsidizedUtility, htarget_pay, hdev_pay]
      simp only [add_zero]
      linarith
    · have hopp : ∀ j : ι, j ≠ i → C j (a j) := by
        intro j hji
        by_contra hj
        exact hother ⟨j, hji, hj⟩
      have hbase := hbest_when_opponents_conform θ i a a' hopp
      have htarget_pay :
          G.conformanceBonusTransfer C B (Function.update a i (σ i (θ i))) i = 0 := by
        have hno_other_update :
            ¬ ∃ j : ι, j ≠ i ∧ ¬ C j (Function.update a i (σ i (θ i)) j) := by
          intro h
          exact hother
            ((conformance_other_update_iff (G := G) C (i := i) a (σ i (θ i))).mp h)
        simp [conformanceBonusTransfer, hσC θ i, hno_other_update]
      have hdev_pay :
          G.conformanceBonusTransfer C B (Function.update a i a') i = 0 := by
        simp [conformanceBonusTransfer, ha']
      rw [subsidizedUtility, subsidizedUtility, htarget_pay, hdev_pay]
      simp only [add_zero]
      exact hbase

/-- The same conformance-bonus construction is a zero-cost signal-blind
ex-post-dominant implementation: on the target path, all players conform, so no
bonus is paid. -/
theorem conformanceBonusTransfer_isSignalBlindExPostDominantKImplementation
    [DecidableEq ι]
    [Fintype ι] (C : ∀ i, G.Act i → Prop)
    {σ : G.StrategyProfile} {M B : ℝ}
    (hB : 0 ≤ B)
    (hσC : ∀ (θ : G.SignalProfile) i, C i (σ i (θ i)))
    (hbound : ∀ θ a i, |G.utility θ a i| ≤ M)
    (hbonus : 2 * M ≤ B)
    (hbest_conforming_deviation :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        C i a' →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i)
    (hbest_when_opponents_conform :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        (∀ j : ι, j ≠ i → C j (a j)) →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i) :
    G.IsSignalBlindExPostDominantKImplementation
      (G.conformanceBonusTransfer C B) σ 0 := by
  classical
  refine ⟨conformanceBonusTransfer_nonneg (G := G) C hB, ?_, ?_⟩
  · exact conformanceBonusTransfer_isExPostDominantProfile (G := G) C hσC hbound
      hbonus hbest_conforming_deviation hbest_when_opponents_conform
  · intro θ
    have hpay_zero : ∀ i, G.conformanceBonusTransfer C B (G.play σ θ) i = 0 := by
      intro i
      have hno_other : ¬ ∃ j : ι, j ≠ i ∧ ¬ C j (G.play σ θ j) := by
        rintro ⟨j, _, hj⟩
        exact hj (by simpa [play] using hσC θ j)
      have hcond_false :
          ¬ (C i (G.play σ θ i) ∧ ∃ j : ι, j ≠ i ∧ ¬ C j (G.play σ θ j)) := by
        intro hcond
        exact hno_other hcond.2
      rw [conformanceBonusTransfer, if_neg hcond_false]
    simp [hpay_zero]

/-- Equivalence-class form of the conformance-bonus theorem. The same weak
hypotheses used for ex-post dominance characterize all undominated
signal-contingent strategy profiles: they are exactly the profiles equivalent
to the target strategy profile under the subsidized utility contexts. -/
theorem conformanceBonusTransfer_undominatedStrategyProfiles_eq
    [DecidableEq ι]
    (C : ∀ i, G.Act i → Prop)
    {σ : G.StrategyProfile} {M B : ℝ}
    (hσC : ∀ (θ : G.SignalProfile) i, C i (σ i (θ i)))
    (hbound : ∀ θ a i, |G.utility θ a i| ≤ M)
    (hbonus : 2 * M ≤ B)
    (hbest_conforming_deviation :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        C i a' →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i)
    (hbest_when_opponents_conform :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        (∀ j : ι, j ≠ i → C j (a j)) →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i) :
    G.undominatedStrategyProfilesWithTransfer
        (G.conformanceBonusTransfer C B) =
      {τ : G.StrategyProfile |
        ∀ i, G.StrategyEquivalentWithTransfer
          (G.conformanceBonusTransfer C B) i (τ i) (σ i)} := by
  have hdominant :
      G.IsExPostDominantProfileWithTransfer
        (G.conformanceBonusTransfer C B) σ :=
    conformanceBonusTransfer_isExPostDominantProfile (G := G) C hσC hbound
      hbonus hbest_conforming_deviation hbest_when_opponents_conform
  exact hdominant.undominatedStrategyProfiles_eq

/-- Singleton form of the conformance-bonus theorem. Under the weak hypotheses,
the undominated set is a singleton precisely when the target has no distinct
signal-contingent strategy equivalent in all subsidized utility contexts. -/
theorem conformanceBonusTransfer_undominatedStrategyProfiles_eq_singleton_iff
    [DecidableEq ι]
    (C : ∀ i, G.Act i → Prop)
    {σ : G.StrategyProfile} {M B : ℝ}
    (hσC : ∀ (θ : G.SignalProfile) i, C i (σ i (θ i)))
    (hbound : ∀ θ a i, |G.utility θ a i| ≤ M)
    (hbonus : 2 * M ≤ B)
    (hbest_conforming_deviation :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        C i a' →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i)
    (hbest_when_opponents_conform :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        (∀ j : ι, j ≠ i → C j (a j)) →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i) :
    G.undominatedStrategyProfilesWithTransfer
        (G.conformanceBonusTransfer C B) =
        ({σ} : Set G.StrategyProfile) ↔
      ∀ i (c : G.Strategy i),
        G.StrategyEquivalentWithTransfer
          (G.conformanceBonusTransfer C B) i c (σ i) → c = σ i := by
  have hdominant :
      G.IsExPostDominantProfileWithTransfer
        (G.conformanceBonusTransfer C B) σ :=
    conformanceBonusTransfer_isExPostDominantProfile (G := G) C hσC hbound
      hbonus hbest_conforming_deviation hbest_when_opponents_conform
  exact hdominant.undominatedStrategyProfiles_eq_singleton_iff

/-- Strict conformance-bonus implementation theorem. Besides the weak
comparison hypotheses used for ex-post dominance, this assumes explicit strict
witnesses for conforming deviations and an available nonconforming opponent
action to punish nonconforming deviations. These are exactly the extra facts
needed to upgrade ex-post dominance to singleton implementation by undominated
signal-contingent strategies. -/
theorem conformanceBonusTransfer_isSignalBlindKImplementation_of_strict
    [DecidableEq ι]
    [Fintype ι] (C : ∀ i, G.Act i → Prop)
    {σ : G.StrategyProfile} {M B : ℝ}
    (hB : 0 ≤ B)
    (hσC : ∀ (θ : G.SignalProfile) i, C i (σ i (θ i)))
    (hsignal : ∀ i (si : G.Signal i), ∃ θ : G.SignalProfile, θ i = si)
    (hbound : ∀ θ a i, |G.utility θ a i| ≤ M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : 2 * M < B)
    (hbest_conforming_deviation :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        C i a' →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i)
    (hbest_when_opponents_conform :
      ∀ (θ : G.SignalProfile) (i : ι) (a : G.ActionProfile) (a' : G.Act i),
        (∀ j : ι, j ≠ i → C j (a j)) →
          G.utility θ (Function.update a i (σ i (θ i))) i ≥
            G.utility θ (Function.update a i a') i)
    (hstrict_conforming_deviation :
      ∀ (i : ι) (si : G.Signal i) (a' : G.Act i),
        C i a' → a' ≠ σ i si →
          ∃ (θ : G.SignalProfile) (a : G.ActionProfile), θ i = si ∧
            G.utility θ (Function.update a i (σ i si)) i >
              G.utility θ (Function.update a i a') i)
    (hopponent_nonconforming :
      ∀ i : ι, ∃ j : ι, j ≠ i ∧ ∃ a : G.Act j, ¬ C j a) :
    G.IsSignalBlindKImplementation
      (G.conformanceBonusTransfer C B) ({σ} : Set G.StrategyProfile) 0 := by
  classical
  let V : G.ActionTransfer := G.conformanceBonusTransfer C B
  have hdominant :
      G.IsExPostDominantProfileWithTransfer V σ :=
    conformanceBonusTransfer_isExPostDominantProfile (G := G) C hσC hbound
      hbonus_weak hbest_conforming_deviation hbest_when_opponents_conform
  have hdominates_ne :
      ∀ (i : ι) (c : G.Strategy i), c ≠ σ i →
        G.WeaklyStrictlyDominatesWithTransfer V i (σ i) c := by
    intro i c hc
    have hdiff : ∃ si : G.Signal i, c si ≠ σ i si := by
      by_contra hnone
      apply hc
      funext si
      by_contra hne
      exact hnone ⟨si, hne⟩
    refine ⟨?_, ?_⟩
    · intro θ a
      exact hdominant i θ a (c (θ i))
    · obtain ⟨si, hcsi⟩ := hdiff
      by_cases hcconf : C i (c si)
      · obtain ⟨θ, a, hθi, hstrict⟩ :=
          hstrict_conforming_deviation i si (c si) hcconf hcsi
        refine ⟨θ, a, ?_⟩
        have hdevC : C i (c (θ i)) := by
          simpa [hθi] using hcconf
        have hpay_eq :
            V (Function.update a i (σ i (θ i))) i =
              V (Function.update a i (c (θ i))) i := by
          have hother :=
            conformance_other_update_iff (G := G) C (i := i) a (σ i (θ i))
          have hother' := conformance_other_update_iff (G := G) C (i := i) a (c (θ i))
          simp [V, conformanceBonusTransfer, hσC θ i, hdevC, hother, hother']
        rw [subsidizedUtility, subsidizedUtility, hpay_eq]
        simpa [hθi] using hstrict
      · obtain ⟨θ, hθi⟩ := hsignal i si
        obtain ⟨j, hji, aj, haj⟩ := hopponent_nonconforming i
        let a : G.ActionProfile := Function.update (G.play σ θ) j aj
        refine ⟨θ, a, ?_⟩
        have hdev_nonconf : ¬ C i (c (θ i)) := by
          simpa [hθi] using hcconf
        have htarget_pay :
            V (Function.update a i (σ i (θ i))) i = B := by
          have hother :
              ∃ k : ι, k ≠ i ∧ ¬ C k (Function.update a i (σ i (θ i)) k) := by
            refine ⟨j, hji, ?_⟩
            simpa [a, Function.update_of_ne hji] using haj
          change G.conformanceBonusTransfer C B
            (Function.update a i (σ i (θ i))) i = B
          rw [conformanceBonusTransfer]
          exact if_pos ⟨by simpa using hσC θ i, hother⟩
        have hdev_pay :
            V (Function.update a i (c (θ i))) i = 0 := by
          change G.conformanceBonusTransfer C B
            (Function.update a i (c (θ i))) i = 0
          rw [conformanceBonusTransfer]
          apply if_neg
          intro h
          exact hdev_nonconf (by simpa using h.1)
        have htarget_lower :
            -M ≤ G.utility θ (Function.update a i (σ i (θ i))) i :=
          neg_le_of_abs_le (hbound θ (Function.update a i (σ i (θ i))) i)
        have hdev_upper :
            G.utility θ (Function.update a i (c (θ i))) i ≤ M :=
          le_of_abs_le (hbound θ (Function.update a i (c (θ i))) i)
        rw [subsidizedUtility, subsidizedUtility, htarget_pay, hdev_pay]
        simp only [add_zero]
        linarith
  have hundom_eq :
      G.undominatedStrategyProfilesWithTransfer V = ({σ} : Set G.StrategyProfile) := by
    ext τ
    constructor
    · intro hτ
      exact Set.mem_singleton_iff.mpr (by
        funext i
        by_contra hne
        exact hτ i (σ i) (hdominates_ne i (τ i) hne))
    · intro hτ
      have hτσ : τ = σ := Set.mem_singleton_iff.mp hτ
      subst τ
      intro i c hcdom
      by_cases hc : c = σ i
      · subst c
        exact WeaklyStrictlyDominatesWithTransfer.irrefl (G := G) (V := V)
          (i := i) (σ i) hcdom
      · have hσc := hdominates_ne i c hc
        exact WeaklyStrictlyDominatesWithTransfer.irrefl (G := G) (V := V)
          (i := i) (σ i) (WeaklyStrictlyDominatesWithTransfer.trans hσc hcdom)
  refine ⟨?_, ?_⟩
  · refine ⟨conformanceBonusTransfer_nonneg (G := G) C hB, ?_, ?_⟩
    · rw [hundom_eq]
      exact Set.singleton_nonempty σ
    · intro τ hτ
      have hτV : τ ∈ G.undominatedStrategyProfilesWithTransfer V := by
        simpa [V] using hτ
      rw [hundom_eq] at hτV
      exact hτV
  · intro τ hτ θ
    have hτσ : τ = σ := Set.mem_singleton_iff.mp (by
      have hτV : τ ∈ G.undominatedStrategyProfilesWithTransfer V := by
        simpa [V] using hτ
      rw [hundom_eq] at hτV
      exact hτV)
    subst τ
    have hpay_zero : ∀ i, V (G.play σ θ) i = 0 := by
      intro i
      have hno_other : ¬ ∃ j : ι, j ≠ i ∧ ¬ C j (G.play σ θ j) := by
        rintro ⟨j, _, hj⟩
        exact hj (by simpa [play] using hσC θ j)
      have hcond_false :
          ¬ (C i (G.play σ θ i) ∧ ∃ j : ι, j ≠ i ∧ ¬ C j (G.play σ θ j)) := by
        intro hcond
        exact hno_other hcond.2
      change G.conformanceBonusTransfer C B (G.play σ θ) i = 0
      rw [conformanceBonusTransfer, if_neg hcond_false]
    exact le_of_eq (Finset.sum_eq_zero fun i _ => hpay_zero i)

end InformationalGame

namespace InformationalGame

variable {ι : Type} [DecidableEq ι] {G : InformationalGame ι}

/-- Payment variables for signal-blind action transfers. -/
abbrev SignalBlindPaymentVar (G : InformationalGame ι) := G.ActionProfile × ι

/-- Read a vector over signal-blind payment variables as an action transfer. -/
def vectorActionTransfer (G : InformationalGame ι)
    (x : G.SignalBlindPaymentVar → ℝ) : G.ActionTransfer :=
  fun a i => x (a, i)

/-- Rows of the signal-blind ex-post-dominance difference system for a fixed
strategy profile.  A row records player `i`, a signal profile, an opponent
action column, and a deviating action. -/
abbrev SignalBlindDominanceRow (G : InformationalGame ι) : Type :=
  Σ i : ι, G.SignalProfile × G.ActionProfile × G.Act i

namespace SignalBlindDominanceMatrix

open Math.LinearProgramming

/-- Coefficients for the transfer difference `V target i - V dev i`. -/
noncomputable def diffCoeff (G : InformationalGame ι) (i : ι)
    (target dev : G.ActionProfile) : G.SignalBlindPaymentVar → ℝ := by
  classical
  exact fun q =>
    (if q = (target, i) then (1 : ℝ) else 0) -
      if q = (dev, i) then (1 : ℝ) else 0

/-- Coefficient matrix for nonnegative signal-blind transfers making `σ`
ex-post dominant. -/
noncomputable def A (G : InformationalGame ι) (σ : G.StrategyProfile) :
    G.SignalBlindDominanceRow → G.SignalBlindPaymentVar → ℝ :=
  fun row =>
    diffCoeff G row.1
      (Function.update row.2.2.1 row.1 (σ row.1 (row.2.1 row.1)))
      (Function.update row.2.2.1 row.1 row.2.2.2)

/-- Right-hand side for the signal-blind ex-post-dominance matrix. -/
noncomputable def b (G : InformationalGame ι) (σ : G.StrategyProfile) :
    G.SignalBlindDominanceRow → ℝ :=
  fun row =>
    G.utility row.2.1 (Function.update row.2.2.1 row.1 row.2.2.2) row.1 -
      G.utility row.2.1
        (Function.update row.2.2.1 row.1 (σ row.1 (row.2.1 row.1))) row.1

theorem rowEval_diffCoeff [Fintype ι] [Fintype G.ActionProfile]
    {Row : Type} (r : Row)
    (x : G.SignalBlindPaymentVar → ℝ) (i : ι)
    (target dev : G.ActionProfile) :
    rowEval (fun _ q => diffCoeff G i target dev q) x r =
      x (target, i) - x (dev, i) := by
  classical
  dsimp [rowEval]
  simp [diffCoeff, sub_mul, Finset.sum_sub_distrib]

/-- Each signal-blind difference row has zero total coefficient: it only
transfers one unit of mass from a deviating action profile to the target one. -/
theorem sum_diffCoeff [Fintype ι] [Fintype G.ActionProfile]
    (i : ι) (target dev : G.ActionProfile) :
    (∑ q : G.SignalBlindPaymentVar, diffCoeff G i target dev q) = 0 := by
  classical
  letI : DecidableEq G.ActionProfile := Classical.decEq G.ActionProfile
  letI : DecidableEq G.SignalBlindPaymentVar := Classical.decEq G.SignalBlindPaymentVar
  simp only [diffCoeff, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (target, i)]
  · rw [Finset.sum_eq_single (dev, i)]
    · simp
    · intro y _hy hy
      simp [hy]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ (dev, i)))
  · intro y _hy hy
    simp [hy]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ (target, i)))

/-- Every row of the signal-blind dominance matrix has zero total coefficient. -/
theorem sum_A_row [Fintype ι] [Fintype G.ActionProfile]
    {σ : G.StrategyProfile} (row : G.SignalBlindDominanceRow) :
    (∑ q : G.SignalBlindPaymentVar, A G σ row q) = 0 := by
  rcases row with ⟨i, θ, a, a'⟩
  exact sum_diffCoeff (G := G) i
    (Function.update a i (σ i (θ i))) (Function.update a i a')

/-- Summing the column imbalances of the signal-blind dominance matrix always
gives zero. -/
theorem sum_colEval_A [Fintype ι] [Fintype G.ActionProfile]
    [Fintype G.SignalProfile] [∀ i, Fintype (G.Act i)]
    {σ : G.StrategyProfile} (y : G.SignalBlindDominanceRow → ℝ) :
    (∑ q : G.SignalBlindPaymentVar, colEval (A G σ) y q) = 0 := by
  classical
  calc
    (∑ q : G.SignalBlindPaymentVar, colEval (A G σ) y q) =
        ∑ q : G.SignalBlindPaymentVar, ∑ row : G.SignalBlindDominanceRow,
          y row * A G σ row q := rfl
    _ = ∑ row : G.SignalBlindDominanceRow, ∑ q : G.SignalBlindPaymentVar,
          y row * A G σ row q := by
          rw [Finset.sum_comm]
    _ = ∑ row : G.SignalBlindDominanceRow,
          y row * ∑ q : G.SignalBlindPaymentVar, A G σ row q := by
          simp [Finset.mul_sum]
    _ = 0 := by
          simp [sum_A_row]

/-- A dual obstruction with nonpositive column imbalance is actually balanced:
all column imbalances are zero.  This is the circulation fact behind the
positive-cycle interpretation of signal-blind infeasibility certificates. -/
theorem colEval_eq_zero_of_forall_colEval_nonpos
    [Fintype ι] [Fintype G.ActionProfile]
    [Fintype G.SignalProfile] [∀ i, Fintype (G.Act i)]
    {σ : G.StrategyProfile} {y : G.SignalBlindDominanceRow → ℝ}
    (hy_col : ∀ q : G.SignalBlindPaymentVar, colEval (A G σ) y q ≤ 0)
    (q : G.SignalBlindPaymentVar) :
    colEval (A G σ) y q = 0 := by
  classical
  have hnonneg :
      ∀ q : G.SignalBlindPaymentVar, 0 ≤ -colEval (A G σ) y q := by
    intro q
    exact neg_nonneg.mpr (hy_col q)
  have hsum : (∑ q : G.SignalBlindPaymentVar, -colEval (A G σ) y q) = 0 := by
    rw [Finset.sum_neg_distrib, sum_colEval_A (G := G) (σ := σ) y]
    simp
  have hq_zero := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun q _ => hnonneg q)).mp hsum q (Finset.mem_univ q)
  linarith

/-- The signal-blind dominance matrix is exactly ex-post dominance for the
associated nonnegative action transfer. -/
theorem minPrimalFeasible_iff_nonnegative_exPostDominant
    [Fintype ι] [Fintype G.ActionProfile]
    {σ : G.StrategyProfile} {x : G.SignalBlindPaymentVar → ℝ} :
    MinPrimalFeasible (A G σ) (b G σ) x ↔
      (∀ a i, 0 ≤ G.vectorActionTransfer x a i) ∧
        G.IsExPostDominantProfileWithTransfer (G.vectorActionTransfer x) σ := by
  classical
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro a i
      exact hx.1 (a, i)
    · intro i θ a a'
      have hrow := hx.2 ⟨i, θ, a, a'⟩
      rw [subsidizedUtility, subsidizedUtility]
      have hlin :
          G.utility θ (Function.update a i a') i -
              G.utility θ (Function.update a i (σ i (θ i))) i ≤
            x (Function.update a i (σ i (θ i)), i) -
              x (Function.update a i a', i) := by
        change
          G.utility θ (Function.update a i a') i -
              G.utility θ (Function.update a i (σ i (θ i))) i ≤
            rowEval
              (fun _ q =>
                diffCoeff G i (Function.update a i (σ i (θ i)))
                  (Function.update a i a') q)
              x (⟨i, (θ, a, a')⟩ : G.SignalBlindDominanceRow) at hrow
        rw [rowEval_diffCoeff] at hrow
        exact hrow
      change
        G.utility θ (Function.update a i (σ i (θ i))) i +
            x (Function.update a i (σ i (θ i)), i) ≥
          G.utility θ (Function.update a i a') i + x (Function.update a i a', i)
      linarith
  · rintro ⟨hnonneg, hdom⟩
    refine ⟨?_, ?_⟩
    · intro q
      exact hnonneg q.1 q.2
    · rintro ⟨i, θ, a, a'⟩
      have h := hdom i θ a a'
      rw [subsidizedUtility, subsidizedUtility] at h
      have hlin :
          G.utility θ (Function.update a i a') i -
              G.utility θ (Function.update a i (σ i (θ i))) i ≤
            x (Function.update a i (σ i (θ i)), i) -
              x (Function.update a i a', i) := by
        change
          G.utility θ (Function.update a i (σ i (θ i))) i +
              x (Function.update a i (σ i (θ i)), i) ≥
            G.utility θ (Function.update a i a') i + x (Function.update a i a', i) at h
        linarith
      change
        G.utility θ (Function.update a i a') i -
            G.utility θ (Function.update a i (σ i (θ i))) i ≤
          rowEval
            (fun _ q =>
              diffCoeff G i (Function.update a i (σ i (θ i)))
                (Function.update a i a') q)
            x (⟨i, (θ, a, a')⟩ : G.SignalBlindDominanceRow)
      rw [rowEval_diffCoeff]
      exact hlin

/-- Farkas certificate for nonexistence of a nonnegative signal-blind transfer
making a fixed strategy profile ex-post dominant.  This is the finite
difference-constraints surface behind the positive-cycle obstruction below. -/
theorem not_exists_nonnegative_exPostDominant_iff_exists_dual_certificate
    [Fintype ι] [Fintype G.ActionProfile] [Fintype G.SignalProfile]
    [∀ i, Fintype (G.Act i)] {σ : G.StrategyProfile} :
    (¬ ∃ V : G.ActionTransfer,
      (∀ a i, 0 ≤ V a i) ∧ G.IsExPostDominantProfileWithTransfer V σ) ↔
      ∃ y : G.SignalBlindDominanceRow → ℝ,
        Nonnegative y ∧
          (∀ q : G.SignalBlindPaymentVar, colEval (A G σ) y q ≤ 0) ∧
            0 < dot (b G σ) y := by
  classical
  rw [show
      (¬ ∃ V : G.ActionTransfer,
        (∀ a i, 0 ≤ V a i) ∧ G.IsExPostDominantProfileWithTransfer V σ) ↔
        ¬ ∃ x : G.SignalBlindPaymentVar → ℝ,
          MinPrimalFeasible (A G σ) (b G σ) x by
    constructor
    · intro h hmat
      rcases hmat with ⟨x, hx⟩
      exact h ⟨G.vectorActionTransfer x,
        (minPrimalFeasible_iff_nonnegative_exPostDominant (G := G)).mp hx⟩
    · intro h hV
      rcases hV with ⟨V, hV⟩
      let x : G.SignalBlindPaymentVar → ℝ := fun q => V q.1 q.2
      have hxV : G.vectorActionTransfer x = V := by
        ext a i
        rfl
      have hx :
          MinPrimalFeasible (A G σ) (b G σ) x := by
        apply
          (minPrimalFeasible_iff_nonnegative_exPostDominant
            (G := G) (σ := σ) (x := x)).mpr
        simpa [hxV] using hV
      exact h ⟨x, hx⟩]
  exact not_exists_minPrimalFeasible_iff_exists_dual_certificate

/-- Feasibility form of the finite signal-blind dominance certificate:
nonnegative signal-blind transfers making `σ` ex-post dominant exist exactly
when no dual obstruction exists. -/
theorem exists_nonnegative_exPostDominant_iff_not_exists_dual_certificate
    [Fintype ι] [Fintype G.ActionProfile] [Fintype G.SignalProfile]
    [∀ i, Fintype (G.Act i)] {σ : G.StrategyProfile} :
    (∃ V : G.ActionTransfer,
      (∀ a i, 0 ≤ V a i) ∧ G.IsExPostDominantProfileWithTransfer V σ) ↔
      ¬ ∃ y : G.SignalBlindDominanceRow → ℝ,
        Nonnegative y ∧
          (∀ q : G.SignalBlindPaymentVar, colEval (A G σ) y q ≤ 0) ∧
            0 < dot (b G σ) y := by
  classical
  constructor
  · rintro ⟨V, hV⟩ hy
    have hnone :
        ¬ ∃ V : G.ActionTransfer,
          (∀ a i, 0 ≤ V a i) ∧ G.IsExPostDominantProfileWithTransfer V σ :=
      not_exists_nonnegative_exPostDominant_iff_exists_dual_certificate.mpr hy
    exact hnone ⟨V, hV⟩
  · intro hno
    by_contra hnone
    exact hno (not_exists_nonnegative_exPostDominant_iff_exists_dual_certificate.mp hnone)

end SignalBlindDominanceMatrix

/-- A finite signal-blind cycle obstruction to ex-post dominance.  For each
index `k`, ex-post dominance gives a lower bound on the transfer difference
between the target action profile at `k` and a deviating profile.  If those
deviating profiles are the target profiles at a permutation of the indices,
the transfer differences telescope to zero; hence a strictly positive sum of
base-game gaps is impossible. -/
theorem not_exists_signalBlind_exPostDominant_of_positive_cycle
    {κ : Type} [Fintype κ] {i : ι} {σ : G.StrategyProfile}
    (next : Equiv.Perm κ)
    (θ : κ → G.SignalProfile) (a : κ → G.ActionProfile) (dev : κ → G.Act i)
    (hlink : ∀ k,
      Function.update (a k) i (dev k) =
        Function.update (a (next k)) i (σ i (θ (next k) i)))
    (hcycle : 0 < ∑ k,
      (G.utility (θ k) (Function.update (a k) i (dev k)) i -
        G.utility (θ k) (Function.update (a k) i (σ i (θ k i))) i)) :
    ¬ ∃ V : G.ActionTransfer,
      G.IsExPostDominantProfileWithTransfer V σ := by
  rintro ⟨V, hdom⟩
  let target : κ → G.ActionProfile :=
    fun k => Function.update (a k) i (σ i (θ k i))
  let deviation : κ → G.ActionProfile :=
    fun k => Function.update (a k) i (dev k)
  have hgap_le_transfer :
      (∑ k,
        (G.utility (θ k) (deviation k) i -
          G.utility (θ k) (target k) i)) ≤
        ∑ k, (V (target k) i - V (deviation k) i) := by
    refine Finset.sum_le_sum ?_
    intro k _hk
    have hkdom := hdom i (θ k) (a k) (dev k)
    rw [subsidizedUtility, subsidizedUtility] at hkdom
    change G.utility (θ k) (target k) i + V (target k) i ≥
      G.utility (θ k) (deviation k) i + V (deviation k) i at hkdom
    linarith
  have htelescopes :
      (∑ k, (V (target k) i - V (deviation k) i)) = 0 := by
    have hdev : ∀ k, deviation k = target (next k) := by
      intro k
      exact hlink k
    simp_rw [hdev]
    rw [Finset.sum_sub_distrib]
    have hperm :
        (∑ k, V (target (next k)) i) = ∑ k, V (target k) i := by
      simpa using (_root_.Equiv.sum_comp next (fun k => V (target k) i))
    rw [hperm]
    ring
  linarith

/-- A positive signal-blind cycle also yields the standard dual certificate for
infeasibility of the nonnegative signal-blind dominance matrix.  This records
the Farkas view of the cycle obstruction without requiring a separate graph
decomposition theorem. -/
theorem exists_signalBlindDominance_dual_certificate_of_positive_cycle
    [Fintype ι] [Fintype G.ActionProfile] [Fintype G.SignalProfile]
    [∀ i, Fintype (G.Act i)]
    {κ : Type} [Fintype κ] {i : ι} {σ : G.StrategyProfile}
    (next : Equiv.Perm κ)
    (θ : κ → G.SignalProfile) (a : κ → G.ActionProfile) (dev : κ → G.Act i)
    (hlink : ∀ k,
      Function.update (a k) i (dev k) =
        Function.update (a (next k)) i (σ i (θ (next k) i)))
    (hcycle : 0 < ∑ k,
      (G.utility (θ k) (Function.update (a k) i (dev k)) i -
        G.utility (θ k) (Function.update (a k) i (σ i (θ k i))) i)) :
    ∃ y : G.SignalBlindDominanceRow → ℝ,
      Math.LinearProgramming.Nonnegative y ∧
        (∀ q : G.SignalBlindPaymentVar,
          Math.LinearProgramming.colEval
            (SignalBlindDominanceMatrix.A G σ) y q ≤ 0) ∧
          0 < Math.LinearProgramming.dot
            (SignalBlindDominanceMatrix.b G σ) y := by
  have hnone_any :
      ¬ ∃ V : G.ActionTransfer,
        G.IsExPostDominantProfileWithTransfer V σ :=
    G.not_exists_signalBlind_exPostDominant_of_positive_cycle
      next θ a dev hlink hcycle
  have hnone_nonneg :
      ¬ ∃ V : G.ActionTransfer,
        (∀ a i, 0 ≤ V a i) ∧ G.IsExPostDominantProfileWithTransfer V σ := by
    rintro ⟨V, _hnonneg, hdom⟩
    exact hnone_any ⟨V, hdom⟩
  exact
    (show
      (¬ ∃ V : G.ActionTransfer,
        (∀ a i, 0 ≤ V a i) ∧ G.IsExPostDominantProfileWithTransfer V σ) ↔
          ∃ y : G.SignalBlindDominanceRow → ℝ,
            Math.LinearProgramming.Nonnegative y ∧
              (∀ q : G.SignalBlindPaymentVar,
                Math.LinearProgramming.colEval
                  (SignalBlindDominanceMatrix.A G σ) y q ≤ 0) ∧
                0 < Math.LinearProgramming.dot
                  (SignalBlindDominanceMatrix.b G σ) y from
        open SignalBlindDominanceMatrix in
          not_exists_nonnegative_exPostDominant_iff_exists_dual_certificate
            (G := G) (σ := σ)).mp hnone_nonneg

/-- A two-edge signal-blind obstruction to ex-post dominance.  If the target
prescribes action `x` at one signal profile and `y` at another, and the two
dominance inequalities would require both `V(x)-V(y)` and `V(y)-V(x)` to
exceed a positive total gap at the same opponent action column, no
signal-blind transfer can make the target ex-post dominant. -/
theorem not_exists_signalBlind_exPostDominant_of_positive_two_cycle
    {i : ι} {σ : G.StrategyProfile}
    (θ η : G.SignalProfile) (a : G.ActionProfile)
    (hcycle : 0 <
      (G.utility θ (Function.update a i (σ i (η i))) i -
        G.utility θ (Function.update a i (σ i (θ i))) i) +
      (G.utility η (Function.update a i (σ i (θ i))) i -
        G.utility η (Function.update a i (σ i (η i))) i)) :
    ¬ ∃ V : G.ActionTransfer,
      G.IsExPostDominantProfileWithTransfer V σ := by
  let next : Equiv.Perm Bool := Equiv.swap false true
  let signals : Bool → G.SignalProfile := fun b => cond b η θ
  let columns : Bool → G.ActionProfile := fun _ => a
  let deviations : Bool → G.Act i := fun b => cond b (σ i (θ i)) (σ i (η i))
  apply G.not_exists_signalBlind_exPostDominant_of_positive_cycle
    (i := i) (σ := σ) next signals columns deviations
  · intro b
    cases b <;> rfl
  · simp [signals, columns, deviations]
    linarith

end InformationalGame

namespace InformationalImplementationExamples

/-- The two private signals used by each player in Figure 4. -/
inductive Figure4Signal
  | s
  | t
  deriving DecidableEq, Fintype

namespace Figure4Signal

instance : Nonempty Figure4Signal := ⟨s⟩

end Figure4Signal

open Figure4Signal

/-- Player 1's `U` action. Player 2 uses the same carrier, with `false`
read as `L`. -/
abbrev p1U : Bool := false

/-- Player 1's `D` action. Player 2 uses the same carrier, with `true`
read as `R`. -/
abbrev p1D : Bool := true

/-- Player 2's `L` action. -/
abbrev p2L : Bool := false

/-- Player 2's `R` action. -/
abbrev p2R : Bool := true

/-! ### Figure 3: domination -/

/-- Player-1 payoffs in Figure 3. The target strategy is `U` after signal `s`
and `D` after signal `t`. -/
def figure3PayoffP1 (θ1 θ2 : Figure4Signal) (a1 a2 : Bool) : ℝ :=
  match θ1, θ2, a1, a2 with
  | s, s, false, false => 1
  | s, s, false, true => 5
  | s, s, true, false => 0
  | s, s, true, true => 4
  | s, t, false, false => 5
  | s, t, false, true => 1
  | s, t, true, false => 4
  | s, t, true, true => 0
  | t, s, false, false => 0
  | t, s, false, true => 4
  | t, s, true, false => 1
  | t, s, true, true => 5
  | t, t, false, false => 4
  | t, t, false, true => 0
  | t, t, true, false => 5
  | t, t, true, true => 1

/-- Player-2 payoffs in Figure 3, included to make the table faithful even
though the domination claim uses only player 1's payoffs. -/
def figure3PayoffP2 (θ1 θ2 : Figure4Signal) (a1 a2 : Bool) : ℝ :=
  match θ1, θ2, a1, a2 with
  | s, s, false, false => 1
  | s, s, false, true => 2
  | s, s, true, false => 5
  | s, s, true, true => 4
  | s, t, false, false => 0
  | s, t, false, true => 1
  | s, t, true, false => 4
  | s, t, true, true => 5
  | t, s, false, false => 5
  | t, s, false, true => 4
  | t, s, true, false => 1
  | t, s, true, true => 0
  | t, t, false, false => 4
  | t, t, false, true => 5
  | t, t, true, false => 0
  | t, t, true, true => 1

/-- Figure 3 as a prior-free informational game. -/
def figure3Game : InformationalGame (Fin 2) where
  Signal := fun _ => Figure4Signal
  Act := fun _ => Bool
  utility := fun θ a =>
    fun
      | 0 => figure3PayoffP1 (θ 0) (θ 1) (a 0) (a 1)
      | 1 => figure3PayoffP2 (θ 0) (θ 1) (a 0) (a 1)

instance figure3Game_strategy_finite (i : Fin 2) :
    Finite (figure3Game.Strategy i) := by
  change Finite (Figure4Signal → Bool)
  infer_instance

/-- A signal profile for Figure 3. -/
def figure3SignalProfile (θ1 θ2 : Figure4Signal) : figure3Game.SignalProfile :=
  fun i => if i = 0 then θ1 else θ2

/-- An action profile for Figure 3. -/
def figure3ActionProfile (a1 a2 : Bool) : figure3Game.ActionProfile :=
  fun i => if i = 0 then a1 else a2

@[simp] theorem figure3SignalProfile_zero (θ1 θ2 : Figure4Signal) :
    figure3SignalProfile θ1 θ2 0 = θ1 := by
  simp [figure3SignalProfile]

@[simp] theorem figure3SignalProfile_one (θ1 θ2 : Figure4Signal) :
    figure3SignalProfile θ1 θ2 1 = θ2 := by
  simp [figure3SignalProfile]

@[simp] theorem figure3ActionProfile_zero (a1 a2 : Bool) :
    figure3ActionProfile a1 a2 0 = a1 := by
  simp [figure3ActionProfile]

@[simp] theorem figure3ActionProfile_one (a1 a2 : Bool) :
    figure3ActionProfile a1 a2 1 = a2 := by
  simp [figure3ActionProfile]

@[simp] theorem figure3ActionProfile_update_zero (a1 a2 b : Bool) :
    Function.update (figure3ActionProfile a1 a2) 0 b =
      figure3ActionProfile b a2 := by
  funext i
  fin_cases i <;> simp [figure3ActionProfile]

@[simp] theorem figure3Game_utility_zero
    (θ1 θ2 : Figure4Signal) (a1 a2 : Bool) :
    figure3Game.utility (figure3SignalProfile θ1 θ2)
        (figure3ActionProfile a1 a2) 0 =
      figure3PayoffP1 θ1 θ2 a1 a2 := by
  simp [figure3Game, figure3SignalProfile, figure3ActionProfile]

/-- The player-1 strategy displayed under Figure 3: play `U` after `s` and
`D` after `t`. -/
def figure3DominatingP1Strategy : figure3Game.Strategy 0
  | s => p1U
  | t => p1D

theorem figure3DominatingP1Strategy_weaklyDominates
    (c : figure3Game.Strategy 0) :
    figure3Game.WeaklyDominatesWithTransfer (fun _ _ => 0)
      0 figure3DominatingP1Strategy c := by
  intro θ a
  let θ0 := θ 0
  let θ1 := θ 1
  let a0 := a 0
  let a1 := a 1
  have hθ : θ = figure3SignalProfile θ0 θ1 := by
    funext j
    fin_cases j <;> simp [θ0, θ1, figure3SignalProfile]
  have ha : a = figure3ActionProfile a0 a1 := by
    funext j
    fin_cases j <;> simp [a0, a1, figure3ActionProfile]
  rw [hθ, ha]
  cases hs : c s <;>
    cases ht : c t <;>
    cases θ0 <;>
    cases θ1 <;>
    cases a0 <;>
    cases a1 <;>
    simp [InformationalGame.subsidizedUtility, figure3DominatingP1Strategy,
      figure3PayoffP1, hs, ht, p1U, p1D] <;>
    norm_num

/-- Figure 3's domination claim: player 1's strategy `s ↦ U, t ↦ D` dominates
every other signal-contingent strategy of player 1. -/
theorem figure3DominatingP1Strategy_weaklyStrictlyDominates_ne
    (c : figure3Game.Strategy 0) (hc : c ≠ figure3DominatingP1Strategy) :
    figure3Game.WeaklyStrictlyDominatesWithTransfer (fun _ _ => 0)
      0 figure3DominatingP1Strategy c := by
  refine ⟨figure3DominatingP1Strategy_weaklyDominates c, ?_⟩
  cases hs : c s <;> cases ht : c t
  · refine ⟨figure3SignalProfile t s, figure3ActionProfile p1U p2L, ?_⟩
    simp [InformationalGame.subsidizedUtility, figure3DominatingP1Strategy,
      figure3PayoffP1, ht, p1U, p1D]
  · exfalso
    apply hc
    funext θ
    cases θ <;> simp [figure3DominatingP1Strategy, hs, ht, p1U, p1D]
  · refine ⟨figure3SignalProfile s s, figure3ActionProfile p1U p2L, ?_⟩
    simp [InformationalGame.subsidizedUtility, figure3DominatingP1Strategy,
      figure3PayoffP1, hs, p1U]
  · refine ⟨figure3SignalProfile s s, figure3ActionProfile p1U p2L, ?_⟩
    simp [InformationalGame.subsidizedUtility, figure3DominatingP1Strategy,
      figure3PayoffP1, hs, p1U]

/-! ### Figure 4: ex-post equilibrium and signal-blind impossibility -/

/-- Player-1 payoffs in Figure 4. -/
def figure4PayoffP1 (θ1 θ2 : Figure4Signal) (a1 a2 : Bool) : ℝ :=
  match θ1, θ2, a1, a2 with
  | s, s, false, false => 2
  | s, s, false, true => 5
  | s, s, true, false => 1
  | s, s, true, true => 6
  | s, t, false, false => 0
  | s, t, false, true => 3
  | s, t, true, false => 7
  | s, t, true, true => 1
  | t, s, false, false => 0
  | t, s, false, true => 5
  | t, s, true, false => 1
  | t, s, true, true => 6
  | t, t, false, false => 5
  | t, t, false, true => 2
  | t, t, true, false => 4
  | t, t, true, true => 3

/-- Player-2 payoffs in Figure 4. -/
def figure4PayoffP2 (θ1 θ2 : Figure4Signal) (a1 a2 : Bool) : ℝ :=
  match θ1, θ2, a1, a2 with
  | s, s, false, false => 8
  | s, s, false, true => 1
  | s, s, true, false => 5
  | s, s, true, true => 4
  | s, t, false, false => 5
  | s, t, false, true => 6
  | s, t, true, false => 2
  | s, t, true, true => 4
  | t, s, false, false => 2
  | t, s, false, true => 2
  | t, s, true, false => 1
  | t, s, true, true => 0
  | t, t, false, false => 0
  | t, t, false, true => 4
  | t, t, true, false => 2
  | t, t, true, true => 3

/-- Figure 4 as a prior-free informational game. Both players have the same two
signals; player 1 reads `false/true` as `U/D`, while player 2 reads them as
`L/R`. -/
def figure4Game : InformationalGame (Fin 2) where
  Signal := fun _ => Figure4Signal
  Act := fun _ => Bool
  utility := fun θ a =>
    fun
      | 0 => figure4PayoffP1 (θ 0) (θ 1) (a 0) (a 1)
      | 1 => figure4PayoffP2 (θ 0) (θ 1) (a 0) (a 1)

instance figure4Game_strategy_finite (i : Fin 2) :
    Finite (figure4Game.Strategy i) := by
  change Finite (Figure4Signal → Bool)
  infer_instance

instance figure4Game_act_fintype (i : Fin 2) :
    Fintype (figure4Game.Act i) := by
  change Fintype Bool
  infer_instance

instance figure4Game_signalProfile_fintype :
    Fintype figure4Game.SignalProfile := by
  change Fintype (Fin 2 → Figure4Signal)
  infer_instance

instance figure4Game_actionProfile_fintype :
    Fintype figure4Game.ActionProfile := by
  change Fintype (Fin 2 → Bool)
  infer_instance

instance figure4Game_signalBlindDominanceRow_fintype :
    Fintype figure4Game.SignalBlindDominanceRow := by
  change Fintype
    (Σ i : Fin 2, figure4Game.SignalProfile × figure4Game.ActionProfile × Bool)
  infer_instance

/-- A signal profile for Figure 4. -/
def figure4SignalProfile (θ1 θ2 : Figure4Signal) : figure4Game.SignalProfile :=
  fun i => if i = 0 then θ1 else θ2

/-- An action profile for Figure 4. -/
def figure4ActionProfile (a1 a2 : Bool) : figure4Game.ActionProfile :=
  fun i => if i = 0 then a1 else a2

@[simp] theorem figure4SignalProfile_zero (θ1 θ2 : Figure4Signal) :
    figure4SignalProfile θ1 θ2 0 = θ1 := by
  simp [figure4SignalProfile]

@[simp] theorem figure4SignalProfile_one (θ1 θ2 : Figure4Signal) :
    figure4SignalProfile θ1 θ2 1 = θ2 := by
  simp [figure4SignalProfile]

@[simp] theorem figure4ActionProfile_zero (a1 a2 : Bool) :
    figure4ActionProfile a1 a2 0 = a1 := by
  simp [figure4ActionProfile]

@[simp] theorem figure4ActionProfile_one (a1 a2 : Bool) :
    figure4ActionProfile a1 a2 1 = a2 := by
  simp [figure4ActionProfile]

@[simp] theorem figure4ActionProfile_update_zero (a1 a2 b : Bool) :
    Function.update (figure4ActionProfile a1 a2) 0 b =
      figure4ActionProfile b a2 := by
  funext i
  fin_cases i <;> simp [figure4ActionProfile]

@[simp] theorem figure4ActionProfile_update_one (a1 a2 b : Bool) :
    Function.update (figure4ActionProfile a1 a2) 1 b =
      figure4ActionProfile a1 b := by
  funext i
  fin_cases i <;> simp [figure4ActionProfile]

@[simp] theorem figure4Game_utility_zero
    (θ1 θ2 : Figure4Signal) (a1 a2 : Bool) :
    figure4Game.utility (figure4SignalProfile θ1 θ2)
        (figure4ActionProfile a1 a2) 0 =
      figure4PayoffP1 θ1 θ2 a1 a2 := by
  simp [figure4Game, figure4SignalProfile, figure4ActionProfile]

@[simp] theorem figure4Game_utility_one
    (θ1 θ2 : Figure4Signal) (a1 a2 : Bool) :
    figure4Game.utility (figure4SignalProfile θ1 θ2)
        (figure4ActionProfile a1 a2) 1 =
      figure4PayoffP2 θ1 θ2 a1 a2 := by
  simp [figure4Game, figure4SignalProfile, figure4ActionProfile]

/-- The ex-post equilibrium displayed in Figure 4: player 1 plays `U` at `s`
and `D` at `t`; player 2 plays `L` at `s` and `R` at `t`. -/
def figure4Target : figure4Game.StrategyProfile :=
  fun
    | 0 => fun θ =>
        match θ with
        | s => p1U
        | t => p1D
    | 1 => fun θ =>
        match θ with
        | s => p2L
        | t => p2R

@[simp] theorem figure4Target_play (θ1 θ2 : Figure4Signal) :
    figure4Game.play figure4Target (figure4SignalProfile θ1 θ2) =
      figure4ActionProfile
        (match θ1 with
        | s => p1U
        | t => p1D)
        (match θ2 with
        | s => p2L
        | t => p2R) := by
  funext i
  fin_cases i <;> rfl

theorem figure4Target_isExPostEq : figure4Game.IsExPostEq figure4Target := by
  intro θ i a
  let θ0 := θ 0
  let θ1 := θ 1
  have hθ : θ = figure4SignalProfile θ0 θ1 := by
    funext j
    fin_cases j <;> simp [θ0, θ1, figure4SignalProfile]
  rw [hθ]
  cases θ0 <;>
    cases θ1 <;>
    fin_cases i <;>
    cases a <;>
    simp [InformationalGame.play, figure4Game, figure4SignalProfile,
      Function.update, figure4Target, figure4PayoffP1, figure4PayoffP2,
      p1U, p1D, p2L, p2R] <;>
    norm_num

/-- The Figure 4 contradiction: no signal-blind action transfer can make the
displayed ex-post equilibrium profile ex-post dominant. The proof uses only
player 1's incentives at signal states `(s,t)` and `(t,t)` against player 2's
off-path action `L`, producing `0 + x ≥ 7 + y` and `5 + x ≤ 4 + y`. -/
theorem figure4_no_signalBlind_transfer_exPostDominant :
    ¬ ∃ V : figure4Game.ActionTransfer,
      figure4Game.IsExPostDominantProfileWithTransfer V figure4Target := by
  apply InformationalGame.not_exists_signalBlind_exPostDominant_of_positive_two_cycle
    (G := figure4Game) (i := 0) (σ := figure4Target)
    (figure4SignalProfile s t) (figure4SignalProfile t t)
    (figure4ActionProfile p1U p2L)
  norm_num [figure4Game, figure4Target, figure4SignalProfile, figure4ActionProfile,
    figure4PayoffP1, figure4PayoffP2, p1U, p1D, p2L, p2R]

/-- The Figure 4 signal-blind obstruction also has the corresponding finite
dual certificate for the signal-blind dominance matrix. -/
theorem figure4_signalBlindDominance_dual_certificate :
    ∃ y : figure4Game.SignalBlindDominanceRow → ℝ,
      Math.LinearProgramming.Nonnegative y ∧
        (∀ q : figure4Game.SignalBlindPaymentVar,
          Math.LinearProgramming.colEval
            (InformationalGame.SignalBlindDominanceMatrix.A figure4Game figure4Target) y q ≤
              0) ∧
          0 < Math.LinearProgramming.dot
            (InformationalGame.SignalBlindDominanceMatrix.b figure4Game figure4Target) y := by
  have hnone_nonneg :
      ¬ ∃ V : figure4Game.ActionTransfer,
        (∀ a i, 0 ≤ V a i) ∧
          figure4Game.IsExPostDominantProfileWithTransfer V figure4Target := by
    rintro ⟨V, _hV_nonneg, hdom⟩
    exact figure4_no_signalBlind_transfer_exPostDominant ⟨V, hdom⟩
  exact
    (show
      (¬ ∃ V : figure4Game.ActionTransfer,
        (∀ a i, 0 ≤ V a i) ∧
          figure4Game.IsExPostDominantProfileWithTransfer V figure4Target) ↔
          ∃ y : figure4Game.SignalBlindDominanceRow → ℝ,
            Math.LinearProgramming.Nonnegative y ∧
              (∀ q : figure4Game.SignalBlindPaymentVar,
                Math.LinearProgramming.colEval
                  (InformationalGame.SignalBlindDominanceMatrix.A figure4Game figure4Target)
                    y q ≤ 0) ∧
                0 < Math.LinearProgramming.dot
                  (InformationalGame.SignalBlindDominanceMatrix.b figure4Game figure4Target)
                    y from
        open InformationalGame.SignalBlindDominanceMatrix in
          not_exists_nonnegative_exPostDominant_iff_exists_dual_certificate
            (G := figure4Game) (σ := figure4Target)).mp hnone_nonneg

/-- The Figure 4 ex-post equilibrium is not signal-blind implementable by
undominated signal-contingent strategies. The general singleton theorem turns
any such implementation into ex-post dominance, contradicting the two
paper-critical inequalities above. -/
theorem figure4_no_signalBlind_implementation :
    ¬ ∃ V : figure4Game.ActionTransfer,
      figure4Game.IsSignalBlindImplementation V
        ({figure4Target} : Set figure4Game.StrategyProfile) := by
  rintro ⟨V, hV⟩
  have hdom :
      figure4Game.IsExPostDominantProfileWithTransfer V figure4Target :=
    InformationalGame.singleton_signalBlindImplementation_isExPostDominant
      (G := figure4Game) hV
  exact figure4_no_signalBlind_transfer_exPostDominant ⟨V, hdom⟩

/-- Therefore the Figure 4 ex-post equilibrium is not signal-blind
k-implementable at any budget. This is the paper's signal-blind impossibility
claim for implementation by undominated signal-contingent strategies. -/
theorem figure4_no_signalBlind_kImplementation (k : ℝ) :
    ¬ ∃ V : figure4Game.ActionTransfer,
      figure4Game.IsSignalBlindKImplementation V
        ({figure4Target} : Set figure4Game.StrategyProfile) k := by
  rintro ⟨V, hV⟩
  exact figure4_no_signalBlind_implementation ⟨V, hV.implementation⟩

/-- Ex-post-dominant variant of the same obstruction. It does not use
nonnegativity or a budget bound. -/
theorem figure4_no_signalBlind_exPostDominantKImplementation (k : ℝ) :
    ¬ ∃ V : figure4Game.ActionTransfer,
      figure4Game.IsSignalBlindExPostDominantKImplementation V figure4Target k := by
  rintro ⟨V, hV⟩
  exact figure4_no_signalBlind_transfer_exPostDominant
    ⟨V, hV.exPostDominantProfile⟩

end InformationalImplementationExamples

end GameTheory
