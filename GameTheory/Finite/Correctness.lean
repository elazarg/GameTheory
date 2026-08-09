/-
# Correctness of the executable frontend

Every algorithm of `GameTheory.Finite.Algorithm` is proved equal to a *semantic*
predicate of `GameTheory.Core`. No solution concept is redefined here: the
executable layer has boolean procedures, and the meaning of "Nash", "dominates",
"Pareto efficient" stays in Core.

This module may import Core and real-valued semantics; the algorithm module may
not.
-/

import GameTheory.Core
import GameTheory.Finite.Algorithm

noncomputable section

namespace GameTheory.Finite

open Probability

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

namespace TableGame

/-- Compilation into proof semantics: the outcome is the realized action
profile, played deterministically. -/
@[reducible]
def toForm (G : TableGame ι) : GameForm ι where
  sig := G.sig
  play profile := FinDist.pure profile

/-- Rational payoffs become real utilities. -/
def utility (G : TableGame ι) : Utility G.sig :=
  fun outcome who => (G.payoff outcome who : ℝ)

@[simp]
theorem utility_apply (G : TableGame ι) (outcome : Profile G.sig) (who : ι) :
    G.utility outcome who = (G.payoff outcome who : ℝ) := rfl

@[simp]
theorem toForm_play (G : TableGame ι) (profile : Profile G.sig) :
    G.toForm.play profile = FinDist.pure profile := rfl

/-! ## Pure Nash -/

theorem isNash_toForm_iff (G : TableGame ι) (profile : Profile G.sig) :
    IsNash G.toForm (euPreference G.utility) profile ↔
      ∀ (who : ι) (replacement : G.Action who),
        G.payoff (Profile.update profile who replacement) who ≤ G.payoff profile who := by
  rw [isNash_iff]
  exact forall_congr' fun who => forall_congr' fun replacement => by simp

theorem isNash_eq_true_iff (G : TableGame ι) (profile : Profile G.sig) :
    G.isNash profile = true ↔ IsNash G.toForm (euPreference G.utility) profile := by
  rw [isNash_toForm_iff, isNash, decide_eq_true_eq]

/-- The flagship frontend theorem: a profile is enumerated exactly when the
compiled game is Nash there. -/
theorem mem_enumerateNash_iff (G : TableGame ι) (profile : Profile G.sig) :
    profile ∈ G.enumerateNash ↔ IsNash G.toForm (euPreference G.utility) profile := by
  rw [enumerateNash, Finset.mem_filter, isNash_eq_true_iff]
  simp

/-! ## Dominance -/

theorem weaklyDominates_eq_true_iff (G : TableGame ι) (who : ι)
    (preferred alternative : G.Action who) :
    G.weaklyDominates who preferred alternative = true ↔
      WeaklyDominates G.toForm (euPreference G.utility) who preferred alternative := by
  rw [weaklyDominates, decide_eq_true_eq]
  exact forall_congr' fun profile => by simp

theorem strictlyDominates_eq_true_iff (G : TableGame ι) (who : ι)
    (preferred alternative : G.Action who) :
    G.strictlyDominates who preferred alternative = true ↔
      StrictlyDominates G.toForm (euPreference G.utility) who preferred alternative := by
  rw [strictlyDominates, decide_eq_true_eq]
  constructor
  · intro hlt profile _
    exact (euPreference_strict_iff _ _ _ _).2 (by simpa using hlt profile)
  · intro hstrict profile
    have := (euPreference_strict_iff _ _ _ _).1 (hstrict profile fun _ => Set.mem_univ _)
    simpa using this

theorem isDominantProfile_eq_true_iff (G : TableGame ι) (profile : Profile G.sig) :
    G.isDominantProfile profile = true ↔
      IsDominantProfile G.toForm (euPreference G.utility) profile := by
  rw [isDominantProfile, decide_eq_true_eq]
  refine forall_congr' fun who => ?_
  rw [isDominant, decide_eq_true_eq]
  exact forall_congr' fun alternative => weaklyDominates_eq_true_iff G who _ alternative

/-- Strict expected-utility preference on a deterministic form is a rational
payoff inequality. -/
theorem strict_euPreference_iff (G : TableGame ι) (who : ι)
    (preferred alternative : Profile G.sig) :
    Preference.strict (euPreference G.utility) who
        (G.toForm.play preferred) (G.toForm.play alternative) ↔
      G.payoff alternative who < G.payoff preferred who := by
  rw [euPreference_strict_iff]
  simp

/-! ## Iterated strict dominance -/

/-- The executable pure-elimination rounds compute the semantic pure survivor
sets. -/
theorem mem_pureSurvivors_iff (G : TableGame ι) :
    ∀ (round : ℕ) (i : ι) (s : G.Action i),
      s ∈ G.pureSurvivors round i ↔
        s ∈ _root_.GameTheory.pureSurvivors G.toForm
          (euPreference G.utility) round i := by
  intro round
  induction round with
  | zero => intro i s; simp [pureSurvivors]
  | succ round ih =>
    intro i s
    rw [pureSurvivors, eliminatePureRound, Finset.mem_filter,
      _root_.GameTheory.mem_pureSurvivors_succ]
    have hprofile : ∀ profile : Profile G.sig,
        (∀ j, profile j ∈ G.pureSurvivors round j) ↔
          (∀ j, profile j ∈ _root_.GameTheory.pureSurvivors G.toForm
            (euPreference G.utility) round j) :=
      fun profile => forall_congr' fun j => ih j (profile j)
    have hdom : ∀ t : G.Action i,
        (∀ profile : Profile G.sig,
          (∀ j, profile j ∈ G.pureSurvivors round j) →
            G.payoff (Profile.update profile i s) i <
              G.payoff (Profile.update profile i t) i) ↔
          StrictlyDominatesOn G.toForm (euPreference G.utility) i
            (_root_.GameTheory.pureSurvivors G.toForm
              (euPreference G.utility) round) t s := by
      intro t
      constructor
      · intro h profile hmem
        exact (strict_euPreference_iff G i _ _).2 (h profile ((hprofile profile).2 hmem))
      · intro h profile hmem
        exact (strict_euPreference_iff G i _ _).1 (h profile ((hprofile profile).1 hmem))
    exact and_congr (ih i s)
      (forall_congr' fun t => imp_congr (ih i t) (not_congr (hdom t)))

/-- The executable pure-stability test is true exactly when the canonical
semantic pure survivor sets have reached a fixed point. -/
theorem pureSurvivorsStable_eq_true_iff (G : TableGame ι) (round : ℕ) :
    G.pureSurvivorsStable round = true ↔
      ∀ i, _root_.GameTheory.pureSurvivors G.toForm
          (euPreference G.utility) (round + 1) i =
        _root_.GameTheory.pureSurvivors G.toForm
          (euPreference G.utility) round i := by
  rw [pureSurvivorsStable, decide_eq_true_eq]
  constructor
  · intro hstable i
    ext s
    rw [← mem_pureSurvivors_iff G, ← mem_pureSurvivors_iff G, hstable i]
  · intro hstable i
    apply Finset.ext
    intro s
    rw [mem_pureSurvivors_iff G, mem_pureSurvivors_iff G, hstable i]

/-- Once the executable survivor iteration reaches a fixed point, every later
round returns the same finite survivor family. -/
theorem pureSurvivors_add_eq_of_pureSurvivorsStable
    (G : TableGame ι) {round : ℕ}
    (hstable : G.pureSurvivorsStable round = true) (later : ℕ) :
    G.pureSurvivors (round + later) = G.pureSurvivors round := by
  rw [pureSurvivorsStable, decide_eq_true_eq] at hstable
  have hstep : G.pureSurvivors (round + 1) = G.pureSurvivors round :=
    funext hstable
  induction later with
  | zero => simp
  | succ later ih =>
    rw [Nat.add_succ, pureSurvivors, ih]
    simpa only [pureSurvivors] using hstep

/-- In particular, executable stability certifies stabilization of the
canonical semantic survivor iteration at every later round. -/
theorem semantic_pureSurvivors_add_eq_of_pureSurvivorsStable
    (G : TableGame ι) {round : ℕ}
    (hstable : G.pureSurvivorsStable round = true) (later : ℕ) :
    _root_.GameTheory.pureSurvivors G.toForm
        (euPreference G.utility) (round + later) =
      _root_.GameTheory.pureSurvivors G.toForm
        (euPreference G.utility) round := by
  funext i
  ext s
  rw [← mem_pureSurvivors_iff G, ← mem_pureSurvivors_iff G,
    pureSurvivors_add_eq_of_pureSurvivorsStable G hstable later]

/-! ## Pareto efficiency -/

theorem paretoDominates_eq_true_iff (G : TableGame ι) (better worse : Profile G.sig) :
    G.paretoDominates better worse = true ↔
      ParetoDominates G.toForm (euPreference G.utility) better worse := by
  rw [paretoDominates, decide_eq_true_eq, ParetoDominates]
  refine and_congr (forall_congr' fun i => by simp) ?_
  exact exists_congr fun i => by
    rw [euPreference_strict_iff]
    simp

theorem isParetoEfficient_eq_true_iff (G : TableGame ι) (profile : Profile G.sig) :
    G.isParetoEfficient profile = true ↔
      IsParetoEfficient G.toForm (euPreference G.utility) profile := by
  rw [isParetoEfficient, decide_eq_true_eq, IsParetoEfficient]
  constructor
  · rintro h ⟨other, hother⟩
    have hdom : G.paretoDominates other profile = true :=
      (paretoDominates_eq_true_iff G other profile).2 hother
    rw [h other] at hdom
    exact Bool.false_ne_true hdom
  · intro h other
    by_contra hne
    exact h ⟨other, (paretoDominates_eq_true_iff G other profile).1 (by simpa using hne)⟩

/-! ## Exact rational mixed profiles -/

theorem isMixed_iff (G : TableGame ι) (mixed : Profile G.mixedSig) :
    G.isMixed mixed = true ↔ ∀ i, (∀ a, 0 ≤ mixed i a) ∧ ∑ a, mixed i a = 1 := by
  rw [isMixed, decide_eq_true_eq]

/-- Compile a verified rational mixed profile into the semantic mixed
extension. -/
def toMixed (G : TableGame ι) (mixed : Profile G.mixedSig) (hmixed : G.isMixed mixed = true) :
    Profile G.sig.mixed :=
  fun i => FinDist.ofWeights (fun a => ((mixed i a : ℚ) : ℝ))
    (fun a => by exact_mod_cast ((isMixed_iff G mixed).1 hmixed i).1 a)
    (by
      have hsum := ((isMixed_iff G mixed).1 hmixed i).2
      have : (((∑ a, mixed i a : ℚ)) : ℝ) = ((1 : ℚ) : ℝ) := by rw [hsum]
      push_cast at this
      simpa using this)

@[simp]
theorem toMixed_prob (G : TableGame ι) (mixed : Profile G.mixedSig)
    (hmixed : G.isMixed mixed = true) (i : ι) (a : G.Action i) :
    (G.toMixed mixed hmixed i).prob a = ((mixed i a : ℚ) : ℝ) :=
  FinDist.prob_ofWeights ..

theorem isMixed_update_pureMixed (G : TableGame ι) (mixed : Profile G.mixedSig)
    (hmixed : G.isMixed mixed = true) (who : ι) (a : G.Action who) :
    G.isMixed (Profile.update mixed who (G.pureMixed who a)) = true := by
  rw [isMixed_iff]
  intro i
  by_cases hi : i = who
  · subst hi
    rw [Profile.update_same]
    exact ⟨fun b => by simp [pureMixed]; split <;> norm_num, by simp [pureMixed]⟩
  · rw [Profile.update_of_ne _ _ hi]
    exact (isMixed_iff G mixed).1 hmixed i

theorem toMixed_update (G : TableGame ι) (mixed : Profile G.mixedSig)
    (hmixed : G.isMixed mixed = true) (who : ι) (a : G.Action who) :
    G.toMixed (Profile.update mixed who (G.pureMixed who a))
        (G.isMixed_update_pureMixed mixed hmixed who a) =
      Profile.update (G.toMixed mixed hmixed) who (FinDist.pure a) := by
  funext i
  refine FinDist.ext_of_prob fun b => ?_
  by_cases hi : i = who
  · subst hi
    rw [toMixed_prob, Profile.update_same, Profile.update_same,
      FinDist.prob_pure_eq_ite, pureMixed]
    split <;> norm_num
  · rw [toMixed_prob, Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi, toMixed_prob]

/-- Exact rational expected payoff agrees with semantic expected utility in the
mixed extension. -/
theorem expectedUtility_toMixed (G : TableGame ι) (mixed : Profile G.mixedSig)
    (hmixed : G.isMixed mixed = true) (who : ι) :
    expectedUtility G.utility who (G.toForm.mixed.play (G.toMixed mixed hmixed)) =
      ((G.expectedPayoff mixed who : ℚ) : ℝ) := by
  have hplay : G.toForm.mixed.play (G.toMixed mixed hmixed) =
      FinDist.pi (G.toMixed mixed hmixed) := by
    rw [GameForm.mixed_play]
    exact FinDist.bind_pure ..
  rw [hplay, expectedUtility, FinDist.expect_eq_sum, expectedPayoff]
  push_cast
  exact Finset.sum_congr rfl fun profile _ => by
    rw [FinDist.prob_pi, mixedWeight]
    push_cast
    exact congrArg₂ _ (Finset.prod_congr rfl fun i _ => toMixed_prob ..) rfl

/-- Exact verification of a supplied rational mixed profile is correct against
the semantic mixed-Nash predicate. -/
theorem verifyMixedNash_eq_true_iff (G : TableGame ι) (mixed : Profile G.mixedSig)
    (hmixed : G.isMixed mixed = true) :
    G.verifyMixedNash mixed = true ↔
      IsNash G.toForm.mixed (euPreference G.utility) (G.toMixed mixed hmixed) := by
  rw [isNash_mixed_iff, verifyMixedNash, hmixed, Bool.true_and, decide_eq_true_eq]
  refine forall_congr' fun who => forall_congr' fun a => ?_
  rw [← toMixed_update G mixed hmixed who a, expectedUtility_toMixed,
    expectedUtility_toMixed, Rat.cast_le]

end TableGame

end GameTheory.Finite
