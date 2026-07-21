/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.GaleShapley.OptionalOrder
import Math.Fintype

/-!
# Proposer strategyproofness of deferred acceptance

This file proves Hwang's blocking-pair theorem and the Dubins--Freedman
"proposers should not lie" result for the proposing side of deferred
acceptance. The proof uses this library's parallel, monotone rejection
operator directly.

The proof architecture follows the Hwang/Dumont argument, informed by
Theodore Hwa's MIT-licensed Lean formalization
`hwatheod/galeshapley-lean`. The definitions and proof are adapted to this
library's `MatchingMarket`, which represents outside options explicitly.

## Main results

* `MatchingMarket.hwang_blocking_pair` -- an arbitrary matching that improves
  some proposer over truthful deferred acceptance has a blocking pair formed
  by a non-improved proposer and the assigned partner of an improved proposer.
* `MatchingMarket.deferredAcceptance_groupStrategyproof` -- if a nonempty
  coalition changes its reports, at least one liar does not strictly improve.
* `MatchingMarket.deferredAcceptance_strategyproof` -- truthful reporting is
  weakly dominant for each individual proposer.
-/

open scoped BigOperators

namespace GameTheory
namespace MatchingMarket

variable {α β : Type} [Fintype α] [Fintype β] (M : MatchingMarket α β)

noncomputable section

/-- The rejection state after `n` parallel deferred-acceptance rounds. -/
def daRejections (n : ℕ) : α → Finset β :=
  M.daStep^[n] (fun _ => ∅)

@[simp]
theorem daRejections_zero : M.daRejections 0 = fun _ => ∅ :=
  rfl

@[simp]
theorem daRejections_succ (n : ℕ) :
    M.daRejections (n + 1) = M.daStep (M.daRejections n) := by
  simp only [daRejections, Function.iterate_succ_apply']

/-- The iterate selected by the termination proof. -/
def daFixedPointRound : ℕ :=
  Classical.choose M.exists_daStep_iterate_fixed

theorem daRejections_fixedPointRound :
    M.daRejections M.daFixedPointRound = M.daFixedPoint :=
  rfl

theorem daRejections_mono {m n : ℕ} (hmn : m ≤ n) (a : α) :
    M.daRejections m a ⊆ M.daRejections n a := by
  induction n, hmn using Nat.le_induction with
  | base => exact fun _ h => h
  | succ n _ ih =>
      rw [M.daRejections_succ n]
      exact fun _ h => M.subset_daStep (M.daRejections n) a (ih h)

omit [Fintype α] in
/-- A current top choice remains the top choice after more rejections provided
that choice itself has not been rejected. -/
theorem topChoice_eq_of_subset_of_not_mem
    {R S : α → Finset β} {a : α} {b : β}
    (hAinj : Function.Injective (M.prefA a))
    (hRS : ∀ a, R a ⊆ S a)
    (htop : M.topChoice R a = some b)
    (hbS : b ∉ S a) :
    M.topChoice S a = some b := by
  have hbR := M.topChoice_mem htop
  have hbSavail : b ∈ M.available S a :=
    M.mem_available.mpr ⟨hbS, (M.mem_available.mp hbR).2⟩
  apply M.topChoice_eq_of_isMax hAinj hbSavail
  intro b' hb'
  apply (M.topChoice_spec htop).2 b'
  exact M.mem_available.mpr
    ⟨fun hb'R => (M.mem_available.mp hb').1 (hRS a hb'R),
      (M.mem_available.mp hb').2⟩

/-- Every iterate through the round after `n` is contained in the selected
fixed point whenever `n` is no later than the selected fixed-point round. -/
theorem daRejections_succ_subset_fixedPoint {n : ℕ}
    (hn : n ≤ M.daFixedPointRound) (a : α) :
    M.daRejections (n + 1) a ⊆ M.daFixedPoint a := by
  rcases lt_or_eq_of_le hn with hlt | rfl
  · rw [← M.daRejections_fixedPointRound]
    exact M.daRejections_mono (Nat.succ_le_iff.mpr hlt) a
  · rw [M.daRejections_succ, M.daRejections_fixedPointRound,
      M.daStep_daFixedPoint]

/-- A newly rejected acceptable proposer loses to the current holder, whom
the receiver strictly prefers under strict receiver preferences. -/
theorem exists_preferred_holder_of_mem_daStep_of_not_mem
    {R : α → Finset β} {a : α} {b : β}
    (hBinj : Function.Injective (M.prefB b))
    (hacc : M.accM b a) (hb : b ∈ M.daStep R a) (hbR : b ∉ R a) :
    ∃ a', M.holder R b = some a' ∧ M.prefB b a < M.prefB b a' := by
  classical
  have hnew : M.topChoice R a = some b ∧ M.holder R b ≠ some a := by
    simpa only [daStep, Finset.mem_union, hbR, false_or,
      Finset.mem_filter, Finset.mem_univ, true_and] using hb
  have hasuit : a ∈ M.suitors R b := M.mem_suitors.mpr ⟨hnew.1, hacc⟩
  obtain ⟨a', ha'⟩ : ∃ a', M.holder R b = some a' :=
    Option.isSome_iff_exists.mp (M.holder_isSome_of_suitors ⟨a, hasuit⟩)
  have hne : a' ≠ a := fun h => hnew.2 (h ▸ ha')
  have hle : M.prefB b a ≤ M.prefB b a' :=
    (M.holder_spec ha').2 a hasuit
  exact ⟨a', ha', lt_of_le_of_ne hle (fun h => hne (hBinj h).symm)⟩

/-- A proposer strictly improves over the truthful deferred-acceptance outcome
under the true optional-partner ranking. -/
def StrictlyImprovesOnDA (μ : α → Option β) (a : α) : Prop :=
  M.prefAOption a (M.daMatching a) < M.prefAOption a (μ a)

/-- Two markets differ only through reports made by proposers. -/
def IsProposerReport (M' : MatchingMarket α β) : Prop :=
  M'.prefB = M.prefB ∧ M'.reserveA = M.reserveA ∧
    M'.reserveB = M.reserveB

/-- A report changes at most the preference of proposer `a`. -/
def IsUnilateralProposerReport (M' : MatchingMarket α β) (a : α) : Prop :=
  M.IsProposerReport M' ∧ ∀ a', a' ≠ a → M'.prefA a' = M.prefA a'

/-- Strict completeness of the true market: every possible partner is strictly
preferred to remaining unmatched on both sides. -/
def HasCompleteAcceptability : Prop :=
  (∀ a b, M.reserveA a < M.prefA a b) ∧
    ∀ b a, M.reserveB b < M.prefB b a

omit [Fintype α] [Fintype β] in
theorem hasCompleteAcceptability_reserveA_ne
    (hcomplete : M.HasCompleteAcceptability) :
    ∀ a b, M.reserveA a ≠ M.prefA a b :=
  fun a b => ne_of_lt (hcomplete.1 a b)

omit [Fintype α] [Fintype β] in
theorem hasCompleteAcceptability_reserveB_ne
    (hcomplete : M.HasCompleteAcceptability) :
    ∀ b a, M.reserveB b ≠ M.prefB b a :=
  fun b a => ne_of_lt (hcomplete.2 b a)

/-- With complete true acceptability, strict improvement necessarily assigns
the proposer an actual partner. -/
theorem assigned_of_strictlyImprovesOnDA
    (hcomplete : M.HasCompleteAcceptability)
    {μ : α → Option β} {a : α}
    (himprove : M.StrictlyImprovesOnDA μ a) :
    ∃ b, μ a = some b := by
  cases hμ : μ a with
  | none =>
      cases hda : M.daMatching a with
      | none => simp [StrictlyImprovesOnDA, hμ, hda] at himprove
      | some b =>
          have := hcomplete.1 a b
          simp [StrictlyImprovesOnDA, hμ, hda] at himprove
          omega
  | some b => exact ⟨b, rfl⟩

/-- The assigned partner of a proposer who improves on truthful deferred
acceptance is matched in the truthful DA outcome. -/
theorem daMatching_partner_exists_of_strictlyImprovesOnDA
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hcomplete : M.HasCompleteAcceptability)
    {μ : α → Option β} {a : α} {b : β}
    (himprove : M.StrictlyImprovesOnDA μ a) (hμa : μ a = some b) :
    ∃ a', M.daMatching a' = some b := by
  classical
  by_contra hnone
  push Not at hnone
  have hpref : M.prefAOption a (M.daMatching a) < M.prefA a b := by
    simpa [StrictlyImprovesOnDA, hμa] using himprove
  apply (M.daMatching_isStable hAinj hBinj).2.2
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro b' hb'
    rw [hb'] at hpref
    simpa using hpref
  · intro ha
    rw [ha] at hpref
    simpa using hpref
  · intro a' ha'
    exact False.elim (hnone a' ha')
  · intro _
    exact hcomplete.2 b a

/-- If an arbitrary matching assigns `b` to a proposer who improves over DA,
then `b` strictly prefers her truthful DA partner to that proposer. -/
theorem daMatching_partner_prefers_improver
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    {μ : α → Option β} {a a' : α} {b : β}
    (himprove : M.StrictlyImprovesOnDA μ a)
    (hμa : μ a = some b) (hdaa' : M.daMatching a' = some b) :
    M.prefB b a < M.prefB b a' := by
  classical
  have hne : a ≠ a' := by
    intro haa'
    subst a'
    simp [StrictlyImprovesOnDA, hμa, hdaa'] at himprove
  by_contra hnot
  have hle : M.prefB b a' ≤ M.prefB b a := le_of_not_gt hnot
  have hlt : M.prefB b a' < M.prefB b a :=
    lt_of_le_of_ne hle (fun he => hne ((hBinj b he).symm))
  have hstable := M.daMatching_isStable hAinj hBinj
  apply hstable.2.2
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro b' hb'
    have hpref : M.prefAOption a (M.daMatching a) < M.prefA a b := by
      simpa [StrictlyImprovesOnDA, hμa] using himprove
    rw [hb'] at hpref
    simpa using hpref
  · intro ha
    have hpref : M.prefAOption a (M.daMatching a) < M.prefA a b := by
      simpa [StrictlyImprovesOnDA, hμa] using himprove
    rw [ha] at hpref
    simpa using hpref
  · intro a'' ha''
    have ha''eq : a'' = a' := hstable.1 a'' a' b ha'' hdaa'
    simpa [ha''eq] using hlt
  · intro hnone
    exact False.elim (hnone a' hdaa')

/-- The easy case of Hwang's argument: if the assigned partner of an improved
proposer is paired by truthful DA with a non-improved proposer, that pair
blocks the arbitrary matching. -/
theorem blockingPair_of_improver_spouse_daMatched_nonimprover
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hcomplete : M.HasCompleteAcceptability)
    {μ : α → Option β} (hμmatching : IsMatching μ)
    {a a' : α} {b : β}
    (himprove : M.StrictlyImprovesOnDA μ a)
    (hμa : μ a = some b) (hdaa' : M.daMatching a' = some b)
    (ha'not : ¬M.StrictlyImprovesOnDA μ a') :
    M.IsBlockingPair μ a' b := by
  classical
  have hne : a ≠ a' := fun haa' => by
    subst a'
    exact ha'not himprove
  have hμa'ne : μ a' ≠ some b := fun hμa' =>
    hne (hμmatching a a' b hμa hμa')
  have hle : M.prefAOption a' (μ a') ≤ M.prefA a' b := by
    have := le_of_not_gt ha'not
    simpa [StrictlyImprovesOnDA, hdaa'] using this
  have hbpref : M.prefB b a < M.prefB b a' :=
    M.daMatching_partner_prefers_improver hAinj hBinj himprove hμa hdaa'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b' hμa'
    have hle' : M.prefA a' b' ≤ M.prefA a' b := by
      simpa [hμa'] using hle
    have hb'ne : b' ≠ b := fun h => hμa'ne (h ▸ hμa')
    exact lt_of_le_of_ne hle' (fun he => hb'ne (hAinj a' he))
  · intro _
    exact hcomplete.1 a' b
  · intro a'' hμa''
    have ha'' : a'' = a := hμmatching a'' a b hμa'' hμa
    simpa [ha''] using hbpref
  · intro hnone
    exact False.elim (hnone a hμa)

/-- **Hwang's theorem.** If an arbitrary valid matching strictly improves some
proposer over the truthful deferred-acceptance outcome, then the arbitrary
matching has a blocking pair consisting of a non-improved proposer and the
assigned partner of an improved proposer.

The true market is assumed complete and strict. The arbitrary matching need
not be stable or individually rational. -/
theorem hwang_blocking_pair
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hcomplete : M.HasCompleteAcceptability)
    {μ : α → Option β} (hμmatching : IsMatching μ)
    (hexists : ∃ a, M.StrictlyImprovesOnDA μ a) :
    ∃ a a' b, μ a = some b ∧ M.StrictlyImprovesOnDA μ a ∧
      ¬M.StrictlyImprovesOnDA μ a' ∧ M.IsBlockingPair μ a' b := by
  classical
  by_cases heasy : ∃ a a' b, M.StrictlyImprovesOnDA μ a ∧
      μ a = some b ∧ M.daMatching a' = some b ∧
        ¬M.StrictlyImprovesOnDA μ a'
  · obtain ⟨a, a', b, ha, hμa, hdaa', ha'⟩ := heasy
    exact ⟨a, a', b, hμa, ha, ha',
      M.blockingPair_of_improver_spouse_daMatched_nonimprover
        hAinj hBinj hcomplete hμmatching ha hμa hdaa' ha'⟩
  · have hdaSpouseImproves {a a' : α} {b : β}
        (ha : M.StrictlyImprovesOnDA μ a)
        (hμa : μ a = some b) (hdaa' : M.daMatching a' = some b) :
        M.StrictlyImprovesOnDA μ a' := by
      by_contra ha'
      exact heasy ⟨a, a', b, ha, hμa, hdaa', ha'⟩
    let R := {a : α // M.StrictlyImprovesOnDA μ a}
    let S := {b : β // ∃ a, M.StrictlyImprovesOnDA μ a ∧ μ a = some b}
    letI : Fintype R := Fintype.ofFinite R
    letI : Fintype S := Fintype.ofFinite S
    have hμAssigned (r : R) : ∃ b, μ r.1 = some b :=
      M.assigned_of_strictlyImprovesOnDA hcomplete r.2
    let μPartner : R → S := fun r =>
      ⟨Classical.choose (hμAssigned r), r.1, r.2,
        Classical.choose_spec (hμAssigned r)⟩
    have hμPartner_spec (r : R) :
        μ r.1 = some (μPartner r).1 := by
      exact Classical.choose_spec (hμAssigned r)
    have hμPartner_bijective : Function.Bijective μPartner := by
      constructor
      · intro r₁ r₂ hr
        apply Subtype.ext
        apply hμmatching r₁.1 r₂.1 (μPartner r₁).1
        · exact hμPartner_spec r₁
        · have hv := congrArg Subtype.val hr
          simpa [hv] using hμPartner_spec r₂
      · intro s
        obtain ⟨a, ha, hμa⟩ := s.2
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Subtype.ext
        exact Option.some.inj ((hμPartner_spec ⟨a, ha⟩).symm.trans hμa)
    have hcardRS : Fintype.card R = Fintype.card S :=
      Fintype.card_congr (Equiv.ofBijective μPartner hμPartner_bijective)
    have hdaAssigned (s : S) : ∃ a', M.daMatching a' = some s.1 := by
      obtain ⟨a, ha, hμa⟩ := s.2
      exact M.daMatching_partner_exists_of_strictlyImprovesOnDA
        hAinj hBinj hcomplete ha hμa
    let daSource : S → R := fun s =>
      ⟨Classical.choose (hdaAssigned s), by
        obtain ⟨a, ha, hμa⟩ := s.2
        exact hdaSpouseImproves ha hμa
          (Classical.choose_spec (hdaAssigned s))⟩
    have hdaSource_spec (s : S) :
        M.daMatching (daSource s).1 = some s.1 := by
      exact Classical.choose_spec (hdaAssigned s)
    have hdaSource_injective : Function.Injective daSource := by
      intro s₁ s₂ hs
      apply Subtype.ext
      have hval : (daSource s₁).1 = (daSource s₂).1 :=
        congrArg Subtype.val hs
      have h₁ := hdaSource_spec s₁
      have h₂ := hdaSource_spec s₂
      rw [hval, h₂] at h₁
      exact (Option.some.inj h₁).symm
    have hdaSource_bijective : Function.Bijective daSource :=
      (Fintype.bijective_iff_injective_and_card daSource).2
        ⟨hdaSource_injective, hcardRS.symm⟩
    have hdaMatched (r : R) : ∃ s : S, M.daMatching r.1 = some s.1 := by
      obtain ⟨s, hs⟩ := hdaSource_bijective.2 r
      refine ⟨s, ?_⟩
      have h := hdaSource_spec s
      simpa [hs] using h
    let daPartner : R → S := fun r => Classical.choose (hdaMatched r)
    have hdaPartner_spec (r : R) :
        M.daMatching r.1 = some (daPartner r).1 :=
      Classical.choose_spec (hdaMatched r)
    let N := M.daFixedPointRound
    have htopFixed (r : R) :
        M.topChoice (M.daRejections N) r.1 = some (daPartner r).1 := by
      rw [M.daRejections_fixedPointRound]
      exact hdaPartner_spec r
    have harrivalExists (r : R) :
        ∃ n, M.topChoice (M.daRejections n) r.1 = some (daPartner r).1 :=
      ⟨N, htopFixed r⟩
    let arrival : R → ℕ := fun r => Nat.find (harrivalExists r)
    have harrival_spec (r : R) :
        M.topChoice (M.daRejections (arrival r)) r.1 =
          some (daPartner r).1 :=
      Nat.find_spec (harrivalExists r)
    have harrival_le_fixed (r : R) : arrival r ≤ N :=
      Nat.find_min' (harrivalExists r) (htopFixed r)
    obtain ⟨a₀, ha₀⟩ := hexists
    let r₀ : R := ⟨a₀, ha₀⟩
    have hRnonempty : (Finset.univ : Finset R).Nonempty :=
      ⟨r₀, Finset.mem_univ r₀⟩
    obtain ⟨r, _, hrmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset R) arrival hRnonempty
    have hrmax' (q : R) : arrival q ≤ arrival r :=
      hrmax q (Finset.mem_univ q)
    let n := arrival r
    let w := (daPartner r).1
    have htopn : M.topChoice (M.daRejections n) r.1 = some w :=
      harrival_spec r
    have hdar : M.daMatching r.1 = some w := hdaPartner_spec r
    have hnfixed : n ≤ N := harrival_le_fixed r
    obtain ⟨r'val, hr'improve, hμr'⟩ := (daPartner r).2
    let r' : R := ⟨r'val, hr'improve⟩
    have hr'ne : r'.1 ≠ r.1 := by
      intro heq
      have hdar' : M.daMatching r'.1 = some w := by
        rw [heq]
        exact hdar
      have hμr'w : μ r'.1 = some w := by simpa [r', w] using hμr'
      have himprove := r'.2
      rw [StrictlyImprovesOnDA, hdar', hμr'w] at himprove
      exact (lt_irrefl _) himprove
    have hfinal_not_rejected (q : R) :
        (daPartner q).1 ∉ M.daFixedPoint q.1 := by
      have htop : M.topChoice M.daFixedPoint q.1 = some (daPartner q).1 := by
        rw [← M.daRejections_fixedPointRound]
        simpa [N] using htopFixed q
      exact (M.mem_available.mp (M.topChoice_mem htop)).1
    have htop_at_n (q : R) (hq : arrival q ≤ n) :
        M.topChoice (M.daRejections n) q.1 = some (daPartner q).1 := by
      have hnot : (daPartner q).1 ∉ M.daRejections n q.1 := by
        intro hmem
        apply hfinal_not_rejected q
        rw [← M.daRejections_fixedPointRound]
        exact M.daRejections_mono (by simpa [N] using hnfixed) q.1 hmem
      exact M.topChoice_eq_of_subset_of_not_mem (hAinj q.1)
        (fun a => M.daRejections_mono hq a) (harrival_spec q) hnot
    have htopr'n :
        M.topChoice (M.daRejections n) r'.1 = some (daPartner r').1 :=
      htop_at_n r' (hrmax' r')
    have hwr' : w ∈ M.daRejections n r'.1 := by
      by_contra hw
      have hwavail : w ∈ M.available (M.daRejections n) r'.1 :=
        M.mem_available.mpr ⟨hw, le_of_lt (hcomplete.1 r'.1 w)⟩
      have hle := (M.topChoice_spec htopr'n).2 w hwavail
      have himprove : M.prefA r'.1 (daPartner r').1 < M.prefA r'.1 w := by
        simpa [StrictlyImprovesOnDA, hdaPartner_spec r', r', hμr'] using r'.2
      omega
    have hnzero : n ≠ 0 := by
      intro hn
      rw [hn] at hwr'
      simp [daRejections] at hwr'
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hnzero
    have hkarr : n = k + 1 := by omega
    have hwstep : w ∈ M.daStep (M.daRejections k) r'.1 := by
      rw [← M.daRejections_succ k, ← hkarr]
      exact hwr'
    obtain ⟨m, hmholder, hr'mpref⟩ :
        ∃ m, M.holder (M.daRejections k) w = some m ∧
          M.prefB w r'.1 < M.prefB w m := by
      by_cases hwold : w ∈ M.daRejections k r'.1
      · rcases M.inv_iterate hAinj hBinj k r'.1 w hwold with hunacc | hholder
        · exact False.elim (hunacc (le_of_lt (hcomplete.2 w r'.1)))
        · exact hholder
      · exact M.exists_preferred_holder_of_mem_daStep_of_not_mem
          (hBinj w) (le_of_lt (hcomplete.2 w r'.1)) hwstep hwold
    have htopn' :
        M.topChoice (M.daRejections (k + 1)) r.1 = some w := by
      simpa [hkarr] using htopn
    have hnfixed' : k + 1 ≤ M.daFixedPointRound := by
      simpa [N, hkarr] using hnfixed
    have hrholder : M.holder (M.daRejections (k + 1)) w = some r.1 := by
      have hrsuit : r.1 ∈ M.suitors (M.daRejections (k + 1)) w :=
        M.mem_suitors.mpr ⟨htopn', le_of_lt (hcomplete.2 w r.1)⟩
      obtain ⟨x, hx⟩ : ∃ x, M.holder (M.daRejections (k + 1)) w = some x :=
        Option.isSome_iff_exists.mp (M.holder_isSome_of_suitors ⟨r.1, hrsuit⟩)
      have hxr : x = r.1 := by
        by_contra hne
        have hholderne :
            M.holder (M.daRejections (k + 1)) w ≠ some r.1 := by
          rw [hx]
          simpa using hne
        have hreject : w ∈ M.daRejections ((k + 1) + 1) r.1 := by
          rw [M.daRejections_succ]
          simp only [daStep, Finset.mem_union, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inr ⟨htopn', hholderne⟩
        exact (hfinal_not_rejected r)
          (M.daRejections_succ_subset_fixedPoint hnfixed' r.1 hreject)
      simpa [hxr] using hx
    have hmsuit : m ∈ M.suitors (M.daRejections (k + 1)) w := by
      simpa [M.daRejections_succ k] using
        M.holder_remains_suitor (hAinj m) hmholder
    have hmtop : M.topChoice (M.daRejections (k + 1)) m = some w :=
      (M.mem_suitors.mp hmsuit).1
    have hmr : m ≠ r.1 := by
      intro hmr
      have htopk : M.topChoice (M.daRejections k) r.1 = some w := by
        have := (M.mem_suitors.mp (M.holder_spec hmholder).1).1
        simpa [hmr] using this
      have hnot := Nat.find_min (harrivalExists r) (by
        change k < arrival r
        simp [n, hkarr])
      exact hnot (by simpa [w] using htopk)
    have hmrejected : w ∈ M.daRejections ((k + 1) + 1) m := by
      have hholderne :
          M.holder (M.daRejections (k + 1)) w ≠ some m := by
        rw [hrholder]
        simpa using hmr.symm
      rw [M.daRejections_succ]
      simp only [daStep, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact Or.inr ⟨hmtop, hholderne⟩
    have hmnot : ¬M.StrictlyImprovesOnDA μ m := by
      intro hmimprove
      let q : R := ⟨m, hmimprove⟩
      have hqtop : M.topChoice (M.daRejections (k + 1)) m =
          some (daPartner q).1 := by
        have h := htop_at_n q (by simpa [n, hkarr] using hrmax' q)
        simpa [n, hkarr, q] using h
      have hqw : (daPartner q).1 = w := by
        exact Option.some.inj (hqtop.symm.trans hmtop)
      have hwfinal : w ∉ M.daFixedPoint m := by
        simpa [q, hqw] using hfinal_not_rejected q
      exact hwfinal
        (M.daRejections_succ_subset_fixedPoint hnfixed' m hmrejected)
    have hwpref : M.prefAOption m (M.daMatching m) < M.prefA m w := by
      cases hda : M.daMatching m with
      | none => simpa [hda] using hcomplete.1 m w
      | some b₀ =>
          have hb₀not : b₀ ∉ M.daRejections (k + 1) m := by
            intro hb₀
            have hb₀final : b₀ ∈ M.daFixedPoint m := by
              rw [← M.daRejections_fixedPointRound]
              exact M.daRejections_mono hnfixed' m hb₀
            have : b₀ ∉ M.daFixedPoint m := by
              exact (M.mem_available.mp (M.topChoice_mem (by
                simpa [daMatching] using hda))).1
            exact this hb₀final
          have hb₀avail : b₀ ∈ M.available (M.daRejections (k + 1)) m :=
            M.mem_available.mpr ⟨hb₀not, le_of_lt (hcomplete.1 m b₀)⟩
          have hle := (M.topChoice_spec hmtop).2 b₀ hb₀avail
          have hb₀ne : b₀ ≠ w := by
            intro heq
            subst b₀
            have hwfinal : w ∈ M.daFixedPoint m :=
              M.daRejections_succ_subset_fixedPoint hnfixed' m hmrejected
            exact (M.mem_available.mp (M.topChoice_mem (by
              simpa [daMatching] using hda))).1 hwfinal
          have hlt : M.prefA m b₀ < M.prefA m w :=
            lt_of_le_of_ne hle (fun he => hb₀ne (hAinj m he))
          simpa [hda] using hlt
    have hμle : M.prefAOption m (μ m) ≤ M.prefAOption m (M.daMatching m) := by
      exact le_of_not_gt hmnot
    have hμpref : M.prefAOption m (μ m) < M.prefA m w :=
      lt_of_le_of_lt hμle hwpref
    refine ⟨r'.1, m, w, hμr', r'.2, hmnot, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b' hμm
      rw [hμm] at hμpref
      simpa using hμpref
    · intro hμm
      rw [hμm] at hμpref
      simpa using hμpref
    · intro a'' hμa''
      have ha'' : a'' = r'.1 := hμmatching a'' r'.1 w hμa'' hμr'
      simpa [ha''] using hr'mpref
    · intro hnone
      exact False.elim (hnone r'.1 hμr')

omit [Fintype α] [Fintype β] in
/-- A blocking-pair judgment is unchanged when receiver preferences and both
outside options agree and the proposer in the pair reports truthfully. -/
theorem isBlockingPair_iff_of_isProposerReport_of_prefA_eq
    {M' : MatchingMarket α β} (hreport : M.IsProposerReport M')
    {μ : α → Option β} {a : α} {b : β}
    (ha : M'.prefA a = M.prefA a) :
    M'.IsBlockingPair μ a b ↔ M.IsBlockingPair μ a b := by
  rcases hreport with ⟨hB, hRA, hRB⟩
  simp only [IsBlockingPair]
  rw [ha, hB, hRA, hRB]

/-- **Dubins--Freedman group strategyproofness.** If proposers change at
least one report, then some proposer whose report changed does not strictly
improve over truthful deferred acceptance.

The true market must be complete and strict. Reported proposer preferences
may reorder or truncate the complete lists, but must remain strict; receiver
preferences and both outside options remain fixed. -/
theorem deferredAcceptance_groupStrategyproof
    {M' : MatchingMarket α β}
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hAinj' : ∀ a, Function.Injective (M'.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hcomplete : M.HasCompleteAcceptability)
    (hreport : M.IsProposerReport M')
    (hchanged : M.prefA ≠ M'.prefA) :
    ∃ a, M.prefA a ≠ M'.prefA a ∧
      ¬M.StrictlyImprovesOnDA M'.daMatching a := by
  classical
  by_contra hcon
  push Not at hcon
  have hliar : ∃ a, M.prefA a ≠ M'.prefA a := by
    by_contra hnone
    push Not at hnone
    exact hchanged (funext hnone)
  have hexists : ∃ a, M.StrictlyImprovesOnDA M'.daMatching a := by
    obtain ⟨a, ha⟩ := hliar
    exact ⟨a, hcon a ha⟩
  have hBinj' : ∀ b, Function.Injective (M'.prefB b) := by
    intro b
    rw [hreport.1]
    exact hBinj b
  have hstable := M'.daMatching_isStable hAinj' hBinj'
  obtain ⟨a, a', b, hmatch, himprove, ha'not, hblock⟩ :=
    M.hwang_blocking_pair hAinj hBinj hcomplete hstable.1 hexists
  have ha'eq : M'.prefA a' = M.prefA a' := by
    by_contra ha'ne
    exact ha'not (hcon a' (Ne.symm ha'ne))
  have hblock' : M'.IsBlockingPair M'.daMatching a' b :=
    (M.isBlockingPair_iff_of_isProposerReport_of_prefA_eq
      hreport ha'eq).2 hblock
  exact hstable.2.2 ⟨a', b, hblock'⟩

/-- **Proposer strategyproofness.** A single proposer cannot obtain a strictly
better partner, according to the true preference, by changing only that
proposer's report to deferred acceptance. -/
theorem deferredAcceptance_strategyproof
    {M' : MatchingMarket α β} (a : α)
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hAinj' : ∀ a, Function.Injective (M'.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hcomplete : M.HasCompleteAcceptability)
    (hreport : M.IsUnilateralProposerReport M' a) :
    ¬M.StrictlyImprovesOnDA M'.daMatching a := by
  classical
  by_cases hchanged : M.prefA = M'.prefA
  · have hmarket : M' = M := by
      cases M
      cases M'
      simp_all [IsUnilateralProposerReport, IsProposerReport]
    subst M'
    exact lt_irrefl _
  · obtain ⟨a', ha'lie, ha'not⟩ :=
      M.deferredAcceptance_groupStrategyproof hAinj hAinj' hBinj
        hcomplete hreport.1 hchanged
    have ha'eq : a' = a := by
      by_contra hne
      exact ha'lie (hreport.2 a' hne).symm
    simpa [ha'eq] using ha'not

end

end MatchingMarket
end GameTheory
