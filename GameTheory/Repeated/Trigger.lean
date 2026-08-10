/-
# Trigger strategies for public repeated play

The trigger remembers the first public stage profile that differs from the
intended path and identifies one differing player. Under a unilateral
deviation, that player is necessarily the deviator; all other players then use
the selected punishment profile. The final theorem packages the standard
one-period-gain versus discounted-tail calculation as ordinary `IsNash`. List
histories avoid dependent-history transport and direct `Function.update` use.
-/

import GameTheory.Repeated.Periodic

noncomputable section

namespace GameTheory

universe uι

variable {ι : Type uι}

namespace UtilityGame

/-- Select one coordinate at which two profiles differ. -/
noncomputable def profileMismatchPlayer (G : UtilityGame ι)
    {expected actual : Profile G.form.sig} (hne : actual ≠ expected) : ι :=
  Classical.choose (by
    by_contra hall
    apply hne
    funext i
    exact not_not.mp (not_exists.mp hall i))

theorem profileMismatchPlayer_spec (G : UtilityGame ι)
    {expected actual : Profile G.form.sig} (hne : actual ≠ expected) :
    actual (G.profileMismatchPlayer hne) ≠
      expected (G.profileMismatchPlayer hne) :=
  Classical.choose_spec (by
    by_contra hall
    apply hne
    funext i
    exact not_not.mp (not_exists.mp hall i))

theorem profileMismatchPlayer_eq_of_other_eq
    (G : UtilityGame ι) {expected actual : Profile G.form.sig}
    (who : ι) (hne : actual ≠ expected)
    (hother : ∀ j, j ≠ who → actual j = expected j) :
    G.profileMismatchPlayer hne = who := by
  by_contra hnot
  exact G.profileMismatchPlayer_spec hne
    (hother _ hnot)

/-- Period `t` is represented in `history` and differs from the intended path. -/
def MismatchAt (G : UtilityGame ι) (path : ℕ → Profile G.form.sig)
    (history : G.ProfileHistory) (t : ℕ) : Prop :=
  ∃ ht : t < history.length,
    history.get ⟨t, ht⟩ ≠ path t

theorem get_ofFn_eq (G : UtilityGame ι)
    (play : ℕ → Profile G.form.sig) (horizon t : ℕ)
    (ht : t < (List.ofFn fun k : Fin horizon => play k).length) :
    (List.ofFn fun k : Fin horizon => play k).get ⟨t, ht⟩ =
      play t := by
  rw [List.get_ofFn]
  congr

theorem mismatchAt_ofFn_iff (G : UtilityGame ι)
    (path play : ℕ → Profile G.form.sig) (horizon t : ℕ) :
    G.MismatchAt path
        (List.ofFn fun k : Fin horizon => play k) t ↔
      t < horizon ∧ play t ≠ path t := by
  constructor
  · rintro ⟨ht, hne⟩
    refine ⟨?_, ?_⟩
    · simpa using ht
    · rw [G.get_ofFn_eq play horizon t ht] at hne
      exact hne
  · rintro ⟨ht, hne⟩
    let ht' : t < (List.ofFn fun k : Fin horizon => play k).length := by
      simpa using ht
    refine ⟨ht', ?_⟩
    rw [G.get_ofFn_eq play horizon t ht']
    exact hne

/-- The first mismatch determines the punishment target. -/
noncomputable def triggerStatus (G : UtilityGame ι)
    (path : ℕ → Profile G.form.sig) (history : G.ProfileHistory) :
    Option ι := by
  classical
  exact
    if hexists : ∃ t, G.MismatchAt path history t then
      let first := Nat.find hexists
      let hfirst := Nat.find_spec hexists
      some (G.profileMismatchPlayer (Classical.choose_spec hfirst))
    else
      none

theorem triggerStatus_ofFn_eq_none (G : UtilityGame ι)
    (path play : ℕ → Profile G.form.sig) (horizon : ℕ)
    (heq : ∀ t < horizon, play t = path t) :
    G.triggerStatus path (List.ofFn fun k : Fin horizon => play k) =
      none := by
  rw [triggerStatus]
  split
  · rename_i hexists
    obtain ⟨t, ht⟩ := hexists
    have hspec := (G.mismatchAt_ofFn_iff path play horizon t).1 ht
    exact False.elim (hspec.2 (heq t hspec.1))
  · rfl

theorem triggerStatus_ofFn_eq_some_of_first
    (G : UtilityGame ι)
    (path play : ℕ → Profile G.form.sig) (who : ι)
    {first horizon : ℕ} (hfirst : first < horizon)
    (hmismatch : play first ≠ path first)
    (hbefore : ∀ t < first, play t = path t)
    (hother : ∀ j, j ≠ who → play first j = path first j) :
    G.triggerStatus path (List.ofFn fun k : Fin horizon => play k) =
      some who := by
  classical
  have hexists :
      ∃ t, G.MismatchAt path
        (List.ofFn fun k : Fin horizon => play k) t :=
    ⟨first, (G.mismatchAt_ofFn_iff path play horizon first).2
      ⟨hfirst, hmismatch⟩⟩
  have hfind : Nat.find hexists = first := by
    apply le_antisymm
    · exact Nat.find_min' hexists
        ((G.mismatchAt_ofFn_iff path play horizon first).2
          ⟨hfirst, hmismatch⟩)
    · apply le_of_not_gt
      intro hlt
      have hspec := (G.mismatchAt_ofFn_iff path play horizon
        (Nat.find hexists)).1 (Nat.find_spec hexists)
      exact hspec.2 (hbefore _ hlt)
  rw [triggerStatus, dif_pos hexists]
  dsimp
  have hselected :
      G.profileMismatchPlayer
          (Classical.choose_spec (Nat.find_spec hexists)) = who := by
    apply G.profileMismatchPlayer_eq_of_other_eq who
    intro j hj
    have hactual :
        (List.ofFn fun k : Fin horizon => play k).get
            ⟨Nat.find hexists, Classical.choose (Nat.find_spec hexists)⟩ =
          play first := by
      rw [G.get_ofFn_eq]
      rw [hfind]
    have hexpected : path (Nat.find hexists) = path first := by
      rw [hfind]
    simpa only [hactual, hexpected] using hother j hj
  rw [hselected]

/-- Follow `path` until the first mismatch, then use the punishment profile
selected for the first differing player. -/
def triggerRepeatedProfile (G : UtilityGame ι)
    (path : ℕ → Profile G.form.sig)
    (punishment : ι → Profile G.form.sig) : G.RepeatedProfile :=
  fun i history =>
    match G.triggerStatus path history with
    | none => path history.length i
    | some deviator => punishment deviator i

/-- With no deviation, the trigger profile generates the intended path. -/
theorem repeatedPlay_triggerRepeatedProfile_eq_path
    (G : UtilityGame ι) (path : ℕ → Profile G.form.sig)
    (punishment : ι → Profile G.form.sig) (t : ℕ) :
    G.repeatedPlay (G.triggerRepeatedProfile path punishment) t =
      path t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      rw [repeatedPlay]
      funext i
      have hstatus := G.triggerStatus_ofFn_eq_none path
        (fun k => G.repeatedPlay
          (G.triggerRepeatedProfile path punishment) k) t
        (fun k hk => ih k hk)
      simp only [triggerRepeatedProfile, List.length_ofFn, hstatus]

/-- Before a unilateral deviation's first path mismatch, realized play remains
on the intended path. -/
theorem repeatedPlay_update_trigger_eq_path_before_first
    (G : UtilityGame ι) [DecidableEq ι]
    (path : ℕ → Profile G.form.sig)
    (punishment : ι → Profile G.form.sig)
    (who : ι) (deviation : G.RepeatedStrategy who)
    {first t : ℕ}
    (hbefore : ∀ k < first,
      G.repeatedPlay
          (Profile.update (G.triggerRepeatedProfile path punishment)
            who deviation) k = path k)
    (ht : t < first) :
    G.repeatedPlay
        (Profile.update (G.triggerRepeatedProfile path punishment)
          who deviation) t = path t :=
  hbefore t ht

/-- At the first path mismatch, every nondeviating coordinate still follows the
intended path. -/
theorem repeatedPlay_update_trigger_other_eq_path_at_first
    (G : UtilityGame ι) [DecidableEq ι]
    (path : ℕ → Profile G.form.sig)
    (punishment : ι → Profile G.form.sig)
    (who : ι) (deviation : G.RepeatedStrategy who)
    {first : ℕ}
    (hbefore : ∀ k < first,
      G.repeatedPlay
          (Profile.update (G.triggerRepeatedProfile path punishment)
            who deviation) k = path k)
    (other : ι) (hother : other ≠ who) :
    G.repeatedPlay
        (Profile.update (G.triggerRepeatedProfile path punishment)
          who deviation) first other =
      path first other := by
  rw [repeatedPlay]
  simp only [Profile.update_of_ne _ _ hother]
  have hstatus := G.triggerStatus_ofFn_eq_none path
    (fun k => G.repeatedPlay
      (Profile.update (G.triggerRepeatedProfile path punishment)
        who deviation) k)
    first hbefore
  simp only [triggerRepeatedProfile, List.length_ofFn, hstatus]

/-- After the first mismatch, every nondeviator uses the selected punishment
profile. -/
theorem repeatedPlay_update_trigger_other_eq_punishment_after_first
    (G : UtilityGame ι) [DecidableEq ι]
    (path : ℕ → Profile G.form.sig)
    (punishment : ι → Profile G.form.sig)
    (who : ι) (deviation : G.RepeatedStrategy who)
    {first t : ℕ} (hfirst : first < t)
    (hmismatch :
      G.repeatedPlay
          (Profile.update (G.triggerRepeatedProfile path punishment)
            who deviation) first ≠ path first)
    (hbefore : ∀ k < first,
      G.repeatedPlay
          (Profile.update (G.triggerRepeatedProfile path punishment)
            who deviation) k = path k)
    (other : ι) (hother : other ≠ who) :
    G.repeatedPlay
        (Profile.update (G.triggerRepeatedProfile path punishment)
          who deviation) t other =
      punishment who other := by
  let deviatingPath : ℕ → Profile G.form.sig :=
    fun k => G.repeatedPlay
      (Profile.update (G.triggerRepeatedProfile path punishment)
        who deviation) k
  have hcoordinate : ∀ j, j ≠ who →
      deviatingPath first j = path first j := by
    intro j hj
    exact G.repeatedPlay_update_trigger_other_eq_path_at_first
      path punishment who deviation hbefore j hj
  have hstatus := G.triggerStatus_ofFn_eq_some_of_first
    path deviatingPath who hfirst hmismatch hbefore hcoordinate
  have hstatus' :
      G.triggerStatus path
          (List.ofFn fun k : Fin t =>
            G.repeatedPlay
              (Profile.update (G.triggerRepeatedProfile path punishment)
                who deviation) k) =
        some who := by
    simpa [deviatingPath] using hstatus
  rw [repeatedPlay]
  simp only [Profile.update_of_ne _ _ hother]
  simp only [triggerRepeatedProfile, hstatus']

/-- After the first mismatch, the realized stage profile is the punishment
profile with only the deviator's coordinate replaced. -/
theorem repeatedPlay_update_trigger_eq_update_punishment_after_first
    (G : UtilityGame ι) [DecidableEq ι]
    (path : ℕ → Profile G.form.sig)
    (punishment : ι → Profile G.form.sig)
    (who : ι) (deviation : G.RepeatedStrategy who)
    {first t : ℕ} (hfirst : first < t)
    (hmismatch :
      G.repeatedPlay
          (Profile.update (G.triggerRepeatedProfile path punishment)
            who deviation) first ≠ path first)
    (hbefore : ∀ k < first,
      G.repeatedPlay
          (Profile.update (G.triggerRepeatedProfile path punishment)
            who deviation) k = path k) :
    G.repeatedPlay
        (Profile.update (G.triggerRepeatedProfile path punishment)
          who deviation) t =
      Profile.update (punishment who) who
        (G.repeatedPlay
          (Profile.update (G.triggerRepeatedProfile path punishment)
            who deviation) t who) := by
  funext other
  by_cases hother : other = who
  · subst hother
    rw [Profile.update_same]
  · rw [Profile.update_of_ne _ _ hother]
    exact G.repeatedPlay_update_trigger_other_eq_punishment_after_first
      path punishment who deviation hfirst hmismatch hbefore other hother

/-- Trigger-strategy Nash criterion. The path continuation stays above the
punishment cap by `margin`, and patience makes that tail loss dominate the
largest one-period gain. -/
theorem triggerRepeatedProfile_isNash
    (G : UtilityGame ι) [DecidableEq ι]
    {discount bound margin : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (path : ℕ → Profile G.form.sig)
    (punishment : ι → Profile G.form.sig)
    (cap : ι → ℝ)
    (hbound : ∀ (who : ι) (stage : Profile G.form.sig),
      |G.stagePayoff stage who| ≤ bound)
    (hpunishment : ∀ (who : ι) (own : G.form.sig.Strategy who),
      G.stagePayoff (Profile.update (punishment who) who own) who ≤
        cap who)
    (hpath : ∀ (who : ι) (start : ℕ),
      cap who + margin ≤
        G.discountedContinuationPayoff discount path start who)
    (hpatient : (1 - discount) * (2 * bound) ≤ discount * margin) :
    IsNash G.repeatedForm (euPreference (G.discountedUtility discount))
      (G.triggerRepeatedProfile path punishment) := by
  classical
  rw [isNash_iff]
  intro who deviation
  rw [euPreference_apply]
  simp only [repeatedForm, expectedUtility_pure, discountedUtility]
  let statusQuo := G.triggerRepeatedProfile path punishment
  let deviatingProfile := Profile.update statusQuo who deviation
  let deviatingPath : ℕ → Profile G.form.sig :=
    fun t => G.repeatedPlay deviatingProfile t
  by_cases hnever : ∀ t, deviatingPath t = path t
  · unfold discountedPayoff GameTheoryMath.normalizedDiscountedSum
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hdiscount1.le)
    apply le_of_eq
    apply tsum_congr
    intro t
    dsimp only
    have hdev :
        G.repeatedPlay
            (Profile.update (G.triggerRepeatedProfile path punishment)
              who deviation) t = path t := by
      simpa [deviatingPath, deviatingProfile, statusQuo] using hnever t
    rw [hdev, G.repeatedPlay_triggerRepeatedProfile_eq_path
      path punishment t]
  · have hexists : ∃ t, deviatingPath t ≠ path t := not_forall.mp hnever
    let first : ℕ := Nat.find hexists
    have hmismatch : deviatingPath first ≠ path first :=
      Nat.find_spec hexists
    have hbefore : ∀ t < first, deviatingPath t = path t := by
      intro t ht
      by_contra hne
      exact Nat.not_lt_of_ge (Nat.find_min' hexists hne) ht
    have htailStage : ∀ k : ℕ,
        G.stagePayoff (deviatingPath (first + 1 + k)) who ≤ cap who := by
      intro k
      have hafter : first < first + 1 + k := by omega
      have hprofile :=
        G.repeatedPlay_update_trigger_eq_update_punishment_after_first
          path punishment who deviation hafter hmismatch hbefore
      have hprofile' :
          deviatingPath (first + 1 + k) =
            Profile.update (punishment who) who
              (deviatingPath (first + 1 + k) who) := by
        simpa [deviatingPath, deviatingProfile, statusQuo] using hprofile
      rw [hprofile']
      exact hpunishment who _
    have hdeviatingTail :
        G.discountedContinuationPayoff discount deviatingPath
            (first + 1) who ≤ cap who := by
      apply G.discountedContinuationPayoff_le_const
        hdiscount0 hdiscount1 deviatingPath (first + 1) who (hbound who)
      intro k
      simpa only [Nat.add_assoc] using htailStage k
    have hfirstComparison :
        G.discountedContinuationPayoff discount deviatingPath first who ≤
          G.discountedContinuationPayoff discount path first who := by
      rw [G.discountedContinuationPayoff_eq_head_add
        hdiscount0 hdiscount1 deviatingPath first who (hbound who)]
      rw [G.discountedContinuationPayoff_eq_head_add
        hdiscount0 hdiscount1 path first who (hbound who)]
      have hdevStage :
          G.stagePayoff (deviatingPath first) who ≤ bound :=
        (abs_le.mp (hbound who (deviatingPath first))).2
      have hpathStage :
          -bound ≤ G.stagePayoff (path first) who :=
        (abs_le.mp (hbound who (path first))).1
      have hpathTail := hpath who (first + 1)
      nlinarith
    have hzero :
        G.discountedContinuationPayoff discount deviatingPath 0 who ≤
          G.discountedContinuationPayoff discount path 0 who := by
      apply G.discountedContinuationPayoff_le_of_prefix_eq_of_tail_le
        hdiscount0 hdiscount1 deviatingPath path 0 first who
        (hbound who)
      · intro k hk
        simpa using hbefore k hk
      · simpa using hfirstComparison
    rw [G.discountedPayoff_eq_discountedContinuationPayoff_zero,
      G.discountedPayoff_eq_discountedContinuationPayoff_zero]
    have hstatusPath :
        (fun t => G.repeatedPlay statusQuo t) = path := by
      funext t
      exact G.repeatedPlay_triggerRepeatedProfile_eq_path
        path punishment t
    calc
      G.discountedContinuationPayoff discount
          (fun t => G.repeatedPlay
            (Profile.update (G.triggerRepeatedProfile path punishment)
              who deviation) t) 0 who =
        G.discountedContinuationPayoff discount deviatingPath 0 who := by
          rfl
      _ ≤ G.discountedContinuationPayoff discount path 0 who := hzero
      _ = G.discountedContinuationPayoff discount
          (fun t => G.repeatedPlay
            (G.triggerRepeatedProfile path punishment) t) 0 who :=
        congrArg
          (fun generated =>
            G.discountedContinuationPayoff discount generated 0 who)
          hstatusPath.symm

end UtilityGame

end GameTheory
