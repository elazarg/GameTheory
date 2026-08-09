/-
# Gale--Shapley deferred acceptance

The algorithm is an inflationary rejection process.  Its data are finite only
at this operation layer; the underlying ordinal market remains capability-free.
The proof follows the mathematical spine of the pinned v1 implementation at
`GameTheory/Cooperative/GaleShapley.lean` (commit
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`), replacing integer maximization by
the canonical relation-valued ranking.
-/

import GameTheory.Cooperative.Matching
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GameTheory

open scoped BigOperators

namespace MatchingMarket

universe uLeft uRight

variable {Left : Type uLeft} {Right : Type uRight}

/-- The order laws needed by deferred acceptance, kept as a theorem-level
certificate rather than stored in the market. -/
structure HasLinearPreferences (market : MatchingMarket Left Right) : Prop where
  left : Preference.Linear market.prefersLeft
  right : Preference.Linear market.prefersRight

variable [Fintype Left] [Fintype Right]
  (market : MatchingMarket Left Right)

/-- A right-side agent is acceptable to a left-side agent. -/
abbrev AcceptableToLeft (left : Left) (right : Right) : Prop :=
  market.prefersLeft left (some right) none

/-- A left-side agent is acceptable to a right-side agent. -/
abbrev AcceptableToRight (right : Right) (left : Left) : Prop :=
  market.prefersRight right (some left) none

open Classical in
/-- Acceptable partners who have not rejected `left`. -/
noncomputable def available
    (rejected : Left → Finset Right) (left : Left) : Finset Right :=
  Finset.univ.filter fun right =>
    right ∉ rejected left ∧ market.AcceptableToLeft left right

omit [Fintype Left] in
theorem mem_available
    {rejected : Left → Finset Right} {left : Left} {right : Right} :
    right ∈ market.available rejected left ↔
      right ∉ rejected left ∧ market.AcceptableToLeft left right := by
  classical
  simp [available]

omit [Fintype Left] in
private theorem exists_best_available
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {left : Left}
    (hne : (market.available rejected left).Nonempty) :
    ∃ best ∈ market.available rejected left,
      ∀ alternative ∈ market.available rejected left,
        market.prefersLeft left (some best) (some alternative) := by
  exact Rank.exists_best_finset
    (fun first middle last h₁ h₂ =>
      (linear.left left).2.1 (some first) (some middle) (some last) h₁ h₂)
    (fun first second =>
      (linear.left left).2.2.1 (some first) (some second)) hne

open Classical in
/-- The best currently available partner, if one exists. -/
noncomputable def topChoice
    (linear : market.HasLinearPreferences)
    (rejected : Left → Finset Right) (left : Left) : Option Right :=
  if hne : (market.available rejected left).Nonempty then
    some (Classical.choose (market.exists_best_available linear hne))
  else
    none

omit [Fintype Left] in
theorem topChoice_spec
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {left : Left} {right : Right}
    (hchoice : market.topChoice linear rejected left = some right) :
    right ∈ market.available rejected left ∧
      ∀ alternative ∈ market.available rejected left,
        market.prefersLeft left (some right) (some alternative) := by
  classical
  unfold topChoice at hchoice
  split at hchoice
  next hne =>
    have hspec := Classical.choose_spec (market.exists_best_available linear hne)
    have heq : Classical.choose (market.exists_best_available linear hne) = right :=
      Option.some.inj hchoice
    simpa [heq] using hspec
  next hne => simp at hchoice

omit [Fintype Left] in
theorem topChoice_mem
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {left : Left} {right : Right}
    (hchoice : market.topChoice linear rejected left = some right) :
    right ∈ market.available rejected left :=
  (market.topChoice_spec linear hchoice).1

omit [Fintype Left] in
theorem acceptableToLeft_of_topChoice
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {left : Left} {right : Right}
    (hchoice : market.topChoice linear rejected left = some right) :
    market.AcceptableToLeft left right :=
  (market.mem_available.mp (market.topChoice_mem linear hchoice)).2

open Classical in
/-- Acceptable left-side agents currently proposing to `right`. -/
noncomputable def suitors
    (linear : market.HasLinearPreferences)
    (rejected : Left → Finset Right) (right : Right) : Finset Left :=
  Finset.univ.filter fun left =>
    market.topChoice linear rejected left = some right ∧
      market.AcceptableToRight right left

theorem mem_suitors
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {left : Left} {right : Right} :
    left ∈ market.suitors linear rejected right ↔
      market.topChoice linear rejected left = some right ∧
        market.AcceptableToRight right left := by
  classical
  simp [suitors]

private theorem exists_best_suitor
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {right : Right}
    (hne : (market.suitors linear rejected right).Nonempty) :
    ∃ best ∈ market.suitors linear rejected right,
      ∀ alternative ∈ market.suitors linear rejected right,
        market.prefersRight right (some best) (some alternative) := by
  exact Rank.exists_best_finset
    (fun first middle last h₁ h₂ =>
      (linear.right right).2.1 (some first) (some middle) (some last) h₁ h₂)
    (fun first second =>
      (linear.right right).2.2.1 (some first) (some second)) hne

open Classical in
/-- The best acceptable suitor currently held by `right`, if any. -/
noncomputable def holder
    (linear : market.HasLinearPreferences)
    (rejected : Left → Finset Right) (right : Right) : Option Left :=
  if hne : (market.suitors linear rejected right).Nonempty then
    some (Classical.choose (market.exists_best_suitor linear hne))
  else
    none

theorem holder_spec
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {right : Right} {left : Left}
    (hholder : market.holder linear rejected right = some left) :
    left ∈ market.suitors linear rejected right ∧
      ∀ alternative ∈ market.suitors linear rejected right,
        market.prefersRight right (some left) (some alternative) := by
  classical
  unfold holder at hholder
  split at hholder
  next hne =>
    have hspec := Classical.choose_spec (market.exists_best_suitor linear hne)
    have heq : Classical.choose (market.exists_best_suitor linear hne) = left :=
      Option.some.inj hholder
    simpa [heq] using hspec
  next hne => simp at hholder

theorem holder_isSome_of_suitors
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {right : Right}
    (hne : (market.suitors linear rejected right).Nonempty) :
    (market.holder linear rejected right).isSome := by
  classical
  simp [holder, hne]

/-- A specified greatest suitor is the uniquely held suitor. -/
theorem holder_eq_of_isBest
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {right : Right} {left : Left}
    (hmem : left ∈ market.suitors linear rejected right)
    (hbest : ∀ alternative ∈ market.suitors linear rejected right,
      market.prefersRight right (some left) (some alternative)) :
    market.holder linear rejected right = some left := by
  classical
  have hne : (market.suitors linear rejected right).Nonempty := ⟨left, hmem⟩
  obtain ⟨held, hheld⟩ :
      ∃ held, market.holder linear rejected right = some held := by
    unfold holder
    rw [dif_pos hne]
    exact ⟨_, rfl⟩
  obtain ⟨hheldMem, hheldBest⟩ := market.holder_spec linear hheld
  have heq : held = left := Option.some.inj <|
    (linear.right right).2.2.2 (some held) (some left)
      (hheldBest left hmem) (hbest held hheldMem)
  simpa [heq] using hheld

open Classical in
/-- One simultaneous deferred-acceptance round. -/
noncomputable def daStep
    (linear : market.HasLinearPreferences)
    (rejected : Left → Finset Right) : Left → Finset Right :=
  fun left => rejected left ∪ Finset.univ.filter fun right =>
    market.topChoice linear rejected left = some right ∧
      market.holder linear rejected right ≠ some left

theorem subset_daStep
    (linear : market.HasLinearPreferences)
    (rejected : Left → Finset Right) (left : Left) :
    rejected left ⊆ market.daStep linear rejected left := by
  classical
  exact Finset.subset_union_left

/-! ## Termination -/

/-- Total rejections accrued by a state. -/
noncomputable def daMeasure (rejected : Left → Finset Right) : ℕ :=
  ∑ left, (rejected left).card

theorem daMeasure_mono
    (linear : market.HasLinearPreferences)
    (rejected : Left → Finset Right) :
    daMeasure rejected ≤ daMeasure (market.daStep linear rejected) := by
  unfold daMeasure
  exact Finset.sum_le_sum fun left _ =>
    Finset.card_le_card (market.subset_daStep linear rejected left)

theorem daMeasure_le (rejected : Left → Finset Right) :
    daMeasure rejected ≤ Fintype.card Left * Fintype.card Right := by
  classical
  unfold daMeasure
  calc
    ∑ left, (rejected left).card ≤ ∑ _left : Left, Fintype.card Right :=
      Finset.sum_le_sum fun left _ =>
        Finset.card_le_card (Finset.subset_univ (rejected left))
    _ = Fintype.card Left * Fintype.card Right := by
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]

/-- Iteration from the empty rejection state reaches a fixed point. -/
theorem exists_daStep_iterate_fixed
    (linear : market.HasLinearPreferences) :
    ∃ rounds : ℕ,
      market.daStep linear
          ((market.daStep linear)^[rounds] (fun _ => ∅)) =
        (market.daStep linear)^[rounds] (fun _ => ∅) := by
  classical
  let step := market.daStep linear
  let initial : Left → Finset Right := fun _ => ∅
  let bound := Fintype.card Left * Fintype.card Right
  have hmono : ∀ rounds,
      daMeasure (step^[rounds] initial) ≤
        daMeasure (step^[rounds + 1] initial) := by
    intro rounds
    rw [Function.iterate_succ_apply']
    exact market.daMeasure_mono linear _
  have hbounded : ∀ rounds, daMeasure (step^[rounds] initial) ≤ bound :=
    fun rounds => daMeasure_le _
  have hstop : ∃ rounds,
      daMeasure (step^[rounds + 1] initial) =
        daMeasure (step^[rounds] initial) := by
    by_contra hnever
    push Not at hnever
    have hstrict : ∀ rounds,
        daMeasure (step^[rounds] initial) <
          daMeasure (step^[rounds + 1] initial) := fun rounds =>
      lt_of_le_of_ne (hmono rounds) (fun heq => hnever rounds heq.symm)
    have hlower : ∀ rounds, rounds ≤ daMeasure (step^[rounds] initial) := by
      intro rounds
      induction rounds with
      | zero => exact Nat.zero_le _
      | succ previous ih =>
          have := hstrict previous
          omega
    have := hlower (bound + 1)
    have := hbounded (bound + 1)
    omega
  obtain ⟨rounds, hmeasure⟩ := hstop
  refine ⟨rounds, ?_⟩
  have hsubset : ∀ left,
      (step^[rounds] initial) left ⊆ step (step^[rounds] initial) left :=
    fun left => market.subset_daStep linear _ left
  have hcard : ∀ left ∈ (Finset.univ : Finset Left),
      ((step^[rounds] initial) left).card ≤
        (step (step^[rounds] initial) left).card :=
    fun left _ => Finset.card_le_card (hsubset left)
  have hsums :
      ∑ left, ((step^[rounds] initial) left).card =
        ∑ left, (step (step^[rounds] initial) left).card := by
    rw [Function.iterate_succ_apply'] at hmeasure
    simpa only [daMeasure] using hmeasure.symm
  have hcards := (Finset.sum_eq_sum_iff_of_le hcard).mp hsums
  funext left
  exact (Finset.eq_of_subset_of_card_le (hsubset left)
    (le_of_eq (hcards left (Finset.mem_univ left)).symm)).symm

/-! ## Fixed-point structure -/

theorem fixedPoint_holder
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right}
    (hfixed : market.daStep linear rejected = rejected)
    {left : Left} {right : Right}
    (hchoice : market.topChoice linear rejected left = some right) :
    market.holder linear rejected right = some left := by
  classical
  by_contra hholder
  have hnotRejected : right ∉ rejected left :=
    (market.mem_available.mp (market.topChoice_mem linear hchoice)).1
  have hnew : right ∈ market.daStep linear rejected left := by
    simp [daStep, hchoice, hholder]
  have heq := congrFun hfixed left
  rw [heq] at hnew
  exact hnotRejected hnew

theorem fixedPoint_isMatching
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right}
    (hfixed : market.daStep linear rejected = rejected) :
    IsMatching (fun left => market.topChoice linear rejected left) := by
  intro left₁ left₂ right h₁ h₂
  have hh₁ := market.fixedPoint_holder linear hfixed h₁
  have hh₂ := market.fixedPoint_holder linear hfixed h₂
  rw [hh₁] at hh₂
  exact Option.some.inj hh₂

theorem fixedPoint_individuallyRational
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right}
    (hfixed : market.daStep linear rejected = rejected) :
    market.IsIndividuallyRational
      (fun left => market.topChoice linear rejected left) := by
  intro left right hchoice
  refine ⟨market.acceptableToLeft_of_topChoice linear hchoice, ?_⟩
  have hholder := market.fixedPoint_holder linear hfixed hchoice
  exact (market.mem_suitors linear).mp (market.holder_spec linear hholder).1 |>.2

theorem available_daStep_subset
    (linear : market.HasLinearPreferences)
    (rejected : Left → Finset Right) (left : Left) :
    market.available (market.daStep linear rejected) left ⊆
      market.available rejected left := by
  classical
  intro right hright
  rw [mem_available] at hright ⊢
  exact ⟨fun h => hright.1 (market.subset_daStep linear rejected left h), hright.2⟩

omit [Fintype Left] in
theorem topChoice_eq_of_isBest
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {left : Left} {right : Right}
    (hmem : right ∈ market.available rejected left)
    (hbest : ∀ alternative ∈ market.available rejected left,
      market.prefersLeft left (some right) (some alternative)) :
    market.topChoice linear rejected left = some right := by
  classical
  have hne : (market.available rejected left).Nonempty := ⟨right, hmem⟩
  obtain ⟨chosen, hchosen⟩ :
      ∃ chosen, market.topChoice linear rejected left = some chosen := by
    unfold topChoice
    rw [dif_pos hne]
    exact ⟨_, rfl⟩
  obtain ⟨hchosenMem, hchosenBest⟩ := market.topChoice_spec linear hchosen
  have heq : chosen = right := Option.some.inj <|
    (linear.left left).2.2.2 (some chosen) (some right)
      (hchosenBest right hmem) (hbest chosen hchosenMem)
  simpa [heq] using hchosen

theorem holder_remains_suitor
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {right : Right} {left : Left}
    (hholder : market.holder linear rejected right = some left) :
    left ∈ market.suitors linear (market.daStep linear rejected) right := by
  classical
  obtain ⟨hchoice, hacceptable⟩ :=
    (market.mem_suitors linear).mp (market.holder_spec linear hholder).1
  have havailable : right ∈ market.available rejected left :=
    market.topChoice_mem linear hchoice
  have hnotRejected : right ∉ market.daStep linear rejected left := by
    simp only [daStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or]
    exact ⟨(market.mem_available.mp havailable).1,
      fun hnew => hnew.2 hholder⟩
  have havailableStep :
      right ∈ market.available (market.daStep linear rejected) left :=
    market.mem_available.mpr
      ⟨hnotRejected, (market.mem_available.mp havailable).2⟩
  have hchoiceStep :
      market.topChoice linear (market.daStep linear rejected) left = some right :=
    market.topChoice_eq_of_isBest linear havailableStep fun alternative halt =>
      (market.topChoice_spec linear hchoice).2 alternative
        (market.available_daStep_subset linear rejected left halt)
  exact (market.mem_suitors linear).mpr ⟨hchoiceStep, hacceptable⟩

theorem holder_improves
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {right : Right} {left : Left}
    (hholder : market.holder linear rejected right = some left) :
    ∃ next,
      market.holder linear (market.daStep linear rejected) right = some next ∧
        market.prefersRight right (some next) (some left) := by
  classical
  have hsuitor := market.holder_remains_suitor linear hholder
  obtain ⟨next, hnext⟩ : ∃ next,
      market.holder linear (market.daStep linear rejected) right = some next :=
    Option.isSome_iff_exists.mp
      (market.holder_isSome_of_suitors linear ⟨left, hsuitor⟩)
  exact ⟨next, hnext, (market.holder_spec linear hnext).2 left hsuitor⟩

/-! ## The rejection invariant and stability -/

/-- Every rejection is justified by unacceptability or a strictly better
currently held suitor. -/
def DeferredAcceptanceInvariant
    (linear : market.HasLinearPreferences)
    (rejected : Left → Finset Right) : Prop :=
  ∀ left right, right ∈ rejected left →
    ¬ market.AcceptableToRight right left ∨
      ∃ held, market.holder linear rejected right = some held ∧
        Preference.strict market.prefersRight right (some held) (some left)

theorem invariant_empty (linear : market.HasLinearPreferences) :
    market.DeferredAcceptanceInvariant linear (fun _ => ∅) := by
  intro left right h
  simp at h

theorem invariant_step
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right}
    (invariant : market.DeferredAcceptanceInvariant linear rejected) :
    market.DeferredAcceptanceInvariant linear
      (market.daStep linear rejected) := by
  classical
  intro left right hreject
  simp only [daStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and] at hreject
  rcases hreject with hold | ⟨hchoice, hnotHeld⟩
  · rcases invariant left right hold with hunacceptable | ⟨held, hheld, hstrict⟩
    · exact Or.inl hunacceptable
    · obtain ⟨next, hnext, himproves⟩ := market.holder_improves linear hheld
      exact Or.inr ⟨next, hnext,
        Rank.trans_strict (linear.right right).2.1 himproves hstrict⟩
  · by_cases hacceptable : market.AcceptableToRight right left
    · have hsuitor : left ∈ market.suitors linear rejected right :=
        (market.mem_suitors linear).mpr ⟨hchoice, hacceptable⟩
      obtain ⟨held, hheld⟩ : ∃ held,
          market.holder linear rejected right = some held :=
        Option.isSome_iff_exists.mp
          (market.holder_isSome_of_suitors linear ⟨left, hsuitor⟩)
      have hne : held ≠ left := fun heq => by
        subst held
        exact hnotHeld hheld
      have hstrict :
          Preference.strict market.prefersRight right (some held) (some left) :=
        Rank.strict_of_le_of_ne (linear.right right).2.2.2
          ((market.holder_spec linear hheld).2 left hsuitor)
          (fun heq => hne (Option.some.inj heq))
      obtain ⟨next, hnext, himproves⟩ := market.holder_improves linear hheld
      exact Or.inr ⟨next, hnext,
        Rank.trans_strict (linear.right right).2.1 himproves hstrict⟩
    · exact Or.inl hacceptable

theorem invariant_iterate
    (linear : market.HasLinearPreferences) (rounds : ℕ) :
    market.DeferredAcceptanceInvariant linear
      ((market.daStep linear)^[rounds] (fun _ => ∅)) := by
  induction rounds with
  | zero => exact market.invariant_empty linear
  | succ previous ih =>
      rw [Function.iterate_succ_apply']
      exact market.invariant_step linear ih

theorem no_blocking_at_fixedPoint
    (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right}
    (hfixed : market.daStep linear rejected = rejected)
    (invariant : market.DeferredAcceptanceInvariant linear rejected) :
    ¬ ∃ left right,
      market.IsBlockingPair
        (fun agent => market.topChoice linear rejected agent) left right := by
  classical
  rintro ⟨left, right, hleft, hrightMatched, hrightNone⟩
  have hacceptableLeft : market.AcceptableToLeft left right := by
    cases hchoice : market.topChoice linear rejected left with
    | none =>
        have hleftNone :
            Preference.strict market.prefersLeft left (some right) none := by
          simpa [hchoice] using hleft
        exact hleftNone.1
    | some current =>
        have hleftCurrent : Preference.strict market.prefersLeft left
            (some right) (some current) := by
          simpa [hchoice] using hleft
        exact (linear.left left).2.1 (some right) (some current) none hleftCurrent.1
          (market.fixedPoint_individuallyRational linear hfixed left current hchoice).1
  have hrejected : right ∈ rejected left := by
    by_contra hnotRejected
    have havailable : right ∈ market.available rejected left :=
      market.mem_available.mpr ⟨hnotRejected, hacceptableLeft⟩
    obtain ⟨current, hcurrent⟩ : ∃ current,
        market.topChoice linear rejected left = some current := by
      unfold topChoice
      rw [dif_pos ⟨right, havailable⟩]
      exact ⟨_, rfl⟩
    have hleftCurrent : Preference.strict market.prefersLeft left
        (some right) (some current) := by
      simpa [hcurrent] using hleft
    exact hleftCurrent.2
      ((market.topChoice_spec linear hcurrent).2 right havailable)
  rcases invariant left right hrejected with hunacceptable | ⟨held, hheld, hstrict⟩
  · apply hunacceptable
    by_cases hmatched : ∃ current,
        market.topChoice linear rejected current = some right
    · obtain ⟨current, hcurrent⟩ := hmatched
      exact (linear.right right).2.1 (some left) (some current) none
        (hrightMatched current hcurrent).1
        (market.fixedPoint_individuallyRational linear hfixed current right hcurrent).2
    · exact (hrightNone (not_exists.mp hmatched)).1
  · have hmatched : market.topChoice linear rejected held = some right :=
      (market.mem_suitors linear).mp (market.holder_spec linear hheld).1 |>.1
    exact (hrightMatched held hmatched).2 hstrict.1

/-! ## Public deferred-acceptance result -/

/-- Rejection state at the first classically selected fixed iterate. -/
noncomputable def daFixedPoint
    (linear : market.HasLinearPreferences) : Left → Finset Right :=
  (market.daStep linear)^[Classical.choose
    (market.exists_daStep_iterate_fixed linear)] (fun _ => ∅)

theorem daStep_daFixedPoint (linear : market.HasLinearPreferences) :
    market.daStep linear (market.daFixedPoint linear) =
      market.daFixedPoint linear :=
  Classical.choose_spec (market.exists_daStep_iterate_fixed linear)

/-- The matching produced by left-proposing deferred acceptance. -/
noncomputable def deferredAcceptance
    (linear : market.HasLinearPreferences) : Matching Left Right :=
  fun left => market.topChoice linear (market.daFixedPoint linear) left

/-- Deferred acceptance produces a stable matching. -/
theorem deferredAcceptance_isStable
    (linear : market.HasLinearPreferences) :
    market.IsStable (market.deferredAcceptance linear) := by
  refine ⟨market.fixedPoint_isMatching linear
      (market.daStep_daFixedPoint linear),
    market.fixedPoint_individuallyRational linear
      (market.daStep_daFixedPoint linear), ?_⟩
  exact market.no_blocking_at_fixedPoint linear
    (market.daStep_daFixedPoint linear) (market.invariant_iterate linear _)

/-- **Gale--Shapley.** Every finite two-sided market with linear ordinal
preferences over optional partners admits a stable matching. -/
theorem exists_stable
    (linear : market.HasLinearPreferences) :
    ∃ matching : Matching Left Right, market.IsStable matching := by
  exact ⟨market.deferredAcceptance linear,
    market.deferredAcceptance_isStable linear⟩

end MatchingMarket

end GameTheory
