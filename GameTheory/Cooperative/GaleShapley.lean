/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Cooperative.Matching

/-!
# Gale–Shapley deferred acceptance and stable-matching existence

The men-proposing deferred-acceptance algorithm, formalized as an **inflationary
rejection operator** on `R : α → Finset β` (the women who have rejected each man).
Iterating from `∅` reaches a fixed point (a bounded, strictly-increasing measure
forces termination), and the fixed-point matching is stable.

Assumes finitely many agents and **strict preferences** (each agent's preference
function is injective).

## Main result

* `MatchingMarket.exists_stable` — every finite market with strict preferences has a
  stable matching.
-/

open scoped BigOperators

namespace GameTheory

namespace MatchingMarket

variable {α β : Type} [Fintype α] [Fintype β] (M : MatchingMarket α β)

/-- Woman `b` is acceptable to man `a`. -/
abbrev accW (a : α) (b : β) : Prop := M.reserveA a ≤ M.prefA a b

/-- Man `a` is acceptable to woman `b`. -/
abbrev accM (b : β) (a : α) : Prop := M.reserveB b ≤ M.prefB b a

open Classical in
/-- Women acceptable to `a` who have not yet rejected him. -/
noncomputable def available (R : α → Finset β) (a : α) : Finset β :=
  Finset.univ.filter (fun b => b ∉ R a ∧ M.accW a b)

open Classical in
/-- Man `a`'s most-preferred available woman, if any. -/
noncomputable def topChoice (R : α → Finset β) (a : α) : Option β :=
  if h : (M.available R a).Nonempty then
    some (Finset.exists_max_image (M.available R a) (M.prefA a) h).choose
  else none

open Classical in
/-- Men currently proposing to `b` whom she finds acceptable. -/
noncomputable def suitors (R : α → Finset β) (b : β) : Finset α :=
  Finset.univ.filter (fun a => M.topChoice R a = some b ∧ M.accM b a)

open Classical in
/-- The man `b` currently holds: her favorite acceptable suitor, if any. -/
noncomputable def holder (R : α → Finset β) (b : β) : Option α :=
  if h : (M.suitors R b).Nonempty then
    some (Finset.exists_max_image (M.suitors R b) (M.prefB b) h).choose
  else none

open Classical in
/-- One deferred-acceptance round: each woman rejects every current proposer she
does not hold. -/
noncomputable def daStep (R : α → Finset β) : α → Finset β := fun a =>
  R a ∪ Finset.univ.filter (fun b => M.topChoice R a = some b ∧ M.holder R b ≠ some a)

/-! ### Specifications of `topChoice` and `holder` -/

omit [Fintype α] in
theorem mem_available {R : α → Finset β} {a : α} {b : β} :
    b ∈ M.available R a ↔ b ∉ R a ∧ M.accW a b := by
  classical
  simp [available]

omit [Fintype α] in
/-- If `a`'s top choice is `b`, then `b` is available and weakly preferred to every
available woman. -/
theorem topChoice_spec {R : α → Finset β} {a : α} {b : β}
    (h : M.topChoice R a = some b) :
    b ∈ M.available R a ∧ ∀ b' ∈ M.available R a, M.prefA a b' ≤ M.prefA a b := by
  classical
  unfold topChoice at h
  split_ifs at h with hne
  obtain ⟨hmem, hmax⟩ := (Finset.exists_max_image (M.available R a) (M.prefA a) hne).choose_spec
  have hb : (Finset.exists_max_image (M.available R a) (M.prefA a) hne).choose = b :=
    Option.some.inj h
  rw [hb] at hmem hmax
  exact ⟨hmem, hmax⟩

omit [Fintype α] in
theorem topChoice_mem {R : α → Finset β} {a : α} {b : β}
    (h : M.topChoice R a = some b) : b ∈ M.available R a :=
  (M.topChoice_spec h).1

omit [Fintype α] in
/-- A man's top choice is acceptable to him. -/
theorem accW_of_topChoice {R : α → Finset β} {a : α} {b : β}
    (h : M.topChoice R a = some b) : M.accW a b :=
  (M.mem_available.mp (M.topChoice_mem h)).2

theorem mem_suitors {R : α → Finset β} {a : α} {b : β} :
    a ∈ M.suitors R b ↔ M.topChoice R a = some b ∧ M.accM b a := by
  classical
  simp [suitors]

/-- If `b` holds `a`, then `a` is a suitor she weakly prefers to every suitor. -/
theorem holder_spec {R : α → Finset β} {b : β} {a : α}
    (h : M.holder R b = some a) :
    a ∈ M.suitors R b ∧ ∀ a' ∈ M.suitors R b, M.prefB b a' ≤ M.prefB b a := by
  classical
  unfold holder at h
  split_ifs at h with hne
  obtain ⟨hmem, hmax⟩ := (Finset.exists_max_image (M.suitors R b) (M.prefB b) hne).choose_spec
  have ha : (Finset.exists_max_image (M.suitors R b) (M.prefB b) hne).choose = a :=
    Option.some.inj h
  rw [ha] at hmem hmax
  exact ⟨hmem, hmax⟩

/-- If `b` has any acceptable suitor, she holds someone. -/
theorem holder_isSome_of_suitors {R : α → Finset β} {b : β}
    (h : (M.suitors R b).Nonempty) : (M.holder R b).isSome := by
  classical
  simp only [holder, dif_pos h, Option.isSome_some]

/-- The deferred-acceptance operator is inflationary: it only ever adds rejections. -/
theorem subset_daStep (R : α → Finset β) (a : α) : R a ⊆ M.daStep R a := by
  classical
  exact Finset.subset_union_left

/-! ### Termination to a fixed point -/

/-- The total number of rejections accrued so far. -/
noncomputable def daMeasure (R : α → Finset β) : ℕ := ∑ a, (R a).card

theorem daMeasure_mono (R : α → Finset β) :
    daMeasure R ≤ daMeasure (M.daStep R) := by
  unfold daMeasure
  exact Finset.sum_le_sum fun a _ => Finset.card_le_card (M.subset_daStep R a)

theorem daMeasure_le (R : α → Finset β) :
    daMeasure R ≤ Fintype.card α * Fintype.card β := by
  classical
  unfold daMeasure
  calc ∑ a, (R a).card ≤ ∑ _a : α, Fintype.card β :=
        Finset.sum_le_sum fun a _ => by
          simpa using Finset.card_le_card (Finset.subset_univ (R a))
    _ = Fintype.card α * Fintype.card β := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Deferred acceptance terminates.** Iterating the round operator from the empty
rejection state reaches a fixed point — exposed here as a specific iterate, so the
deferred-acceptance invariant can be transported to it. -/
theorem exists_daStep_iterate_fixed :
    ∃ n : ℕ, M.daStep (M.daStep^[n] (fun _ => ∅)) = M.daStep^[n] (fun _ => ∅) := by
  classical
  set f := M.daStep with hf
  set R₀ : α → Finset β := fun _ => ∅ with hR0
  set B := Fintype.card α * Fintype.card β with hB
  have hmono : ∀ n, daMeasure (f^[n] R₀) ≤ daMeasure (f^[n + 1] R₀) := by
    intro n
    rw [Function.iterate_succ_apply']
    exact M.daMeasure_mono _
  have hbdd : ∀ n, daMeasure (f^[n] R₀) ≤ B := fun n => daMeasure_le _
  have hstop : ∃ n, daMeasure (f^[n + 1] R₀) = daMeasure (f^[n] R₀) := by
    by_contra hcon
    have hcon' : ∀ n, daMeasure (f^[n + 1] R₀) ≠ daMeasure (f^[n] R₀) := not_exists.mp hcon
    have hstrict : ∀ n, daMeasure (f^[n] R₀) < daMeasure (f^[n + 1] R₀) := fun n =>
      lt_of_le_of_ne (hmono n) (fun he => hcon' n he.symm)
    have hge : ∀ n, n ≤ daMeasure (f^[n] R₀) := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ k ih => have := hstrict k; omega
    have h1 := hge (B + 1)
    have h2 := hbdd (B + 1)
    omega
  obtain ⟨n, hn⟩ := hstop
  refine ⟨n, ?_⟩
  have hsub : ∀ a, (f^[n] R₀) a ⊆ f (f^[n] R₀) a := fun a => M.subset_daStep _ a
  have hle : ∀ a ∈ (Finset.univ : Finset α),
      ((f^[n] R₀) a).card ≤ (f (f^[n] R₀) a).card :=
    fun a _ => Finset.card_le_card (hsub a)
  have hmeq : ∑ a, ((f^[n] R₀) a).card = ∑ a, (f (f^[n] R₀) a).card := by
    have h := hn
    rw [Function.iterate_succ_apply'] at h
    simpa only [daMeasure] using h.symm
  have hcardeq := (Finset.sum_eq_sum_iff_of_le hle).mp hmeq
  funext a
  exact (Finset.eq_of_subset_of_card_le (hsub a)
    (le_of_eq (hcardeq a (Finset.mem_univ a)).symm)).symm

/-! ### The fixed-point matching is a matching and is individually rational -/

/-- At a fixed point, if `a` proposes to `b` then `b` holds `a`: the proposal is
not rejected. -/
theorem fixedPoint_holder {R : α → Finset β} (hR : M.daStep R = R) {a : α} {b : β}
    (h : M.topChoice R a = some b) : M.holder R b = some a := by
  classical
  by_contra hne
  have hb_notin : b ∉ R a := (M.mem_available.mp (M.topChoice_mem h)).1
  have hb_in : b ∈ M.daStep R a := by
    simp only [daStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨h, hne⟩
  rw [hR] at hb_in
  exact hb_notin hb_in

/-- The fixed-point matching: each man is assigned his top remaining choice. -/
theorem fixedPoint_isMatching {R : α → Finset β} (hR : M.daStep R = R) :
    IsMatching (fun a => M.topChoice R a) := by
  intro a₁ a₂ b h₁ h₂
  have e1 := M.fixedPoint_holder hR h₁
  have e2 := M.fixedPoint_holder hR h₂
  rw [e1] at e2
  exact Option.some.inj e2

/-- The fixed-point matching is individually rational. -/
theorem fixedPoint_ir {R : α → Finset β} (hR : M.daStep R = R) (a : α) (b : β)
    (h : M.topChoice R a = some b) :
    M.prefA a b ≥ M.reserveA a ∧ M.prefB b a ≥ M.reserveB b := by
  refine ⟨M.accW_of_topChoice h, ?_⟩
  have hhold := M.fixedPoint_holder hR h
  exact (M.mem_suitors.mp (M.holder_spec hhold).1).2

/-! ### The deferred-acceptance improvement invariant (needs strict preferences) -/

omit [Fintype α] in
/-- Under strict preferences the top choice is the *unique* maximizer of `prefA a`
over the available women. -/
theorem topChoice_eq_of_isMax {R : α → Finset β} {a : α} {b : β}
    (hinj : Function.Injective (M.prefA a)) (hb : b ∈ M.available R a)
    (hmax : ∀ b' ∈ M.available R a, M.prefA a b' ≤ M.prefA a b) :
    M.topChoice R a = some b := by
  classical
  have hne : (M.available R a).Nonempty := ⟨b, hb⟩
  obtain ⟨b', hb'⟩ : ∃ b', M.topChoice R a = some b' := by
    unfold topChoice; rw [dif_pos hne]; exact ⟨_, rfl⟩
  obtain ⟨hmem', hmax'⟩ := M.topChoice_spec hb'
  have : b' = b := hinj (le_antisymm (hmax b' hmem') (hmax' b hb))
  rw [hb', this]

/-- A deferred-acceptance round only removes women from a man's available set. -/
theorem available_daStep_subset (R : α → Finset β) (a : α) :
    M.available (M.daStep R) a ⊆ M.available R a := by
  classical
  intro b hb
  rw [mem_available] at hb ⊢
  exact ⟨fun h => hb.1 (M.subset_daStep R a h), hb.2⟩

/-- A woman never rejects the man she holds: the holder keeps proposing to her after
a round (using strict preferences to pin his top choice). -/
theorem holder_remains_suitor {R : α → Finset β} {b : β} {a'' : α}
    (hinj : Function.Injective (M.prefA a'')) (h : M.holder R b = some a'') :
    a'' ∈ M.suitors (M.daStep R) b := by
  classical
  obtain ⟨htop, hacc⟩ := M.mem_suitors.mp (M.holder_spec h).1
  have hb_avail_R : b ∈ M.available R a'' := M.topChoice_mem htop
  have hb_notin_step : b ∉ M.daStep R a'' := by
    simp only [daStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
    exact ⟨(M.mem_available.mp hb_avail_R).1, fun hcon => hcon.2 h⟩
  have hb_avail_step : b ∈ M.available (M.daStep R) a'' :=
    M.mem_available.mpr ⟨hb_notin_step, (M.mem_available.mp hb_avail_R).2⟩
  have htop_step : M.topChoice (M.daStep R) a'' = some b :=
    M.topChoice_eq_of_isMax hinj hb_avail_step
      (fun b' hb' => (M.topChoice_spec htop).2 b' (M.available_daStep_subset R a'' hb'))
  exact M.mem_suitors.mpr ⟨htop_step, hacc⟩

/-- A woman's held partner only improves across rounds. -/
theorem holder_improve {R : α → Finset β} {b : β} {a'' : α}
    (hinj : Function.Injective (M.prefA a'')) (h : M.holder R b = some a'') :
    ∃ a''', M.holder (M.daStep R) b = some a''' ∧ M.prefB b a'' ≤ M.prefB b a''' := by
  classical
  have hsuit : a'' ∈ M.suitors (M.daStep R) b := M.holder_remains_suitor hinj h
  obtain ⟨a''', ha'''⟩ : ∃ a''', M.holder (M.daStep R) b = some a''' :=
    Option.isSome_iff_exists.mp (M.holder_isSome_of_suitors ⟨a'', hsuit⟩)
  exact ⟨a''', ha''', (M.holder_spec ha''').2 a'' hsuit⟩

/-- The **deferred-acceptance invariant**: every woman who has rejected a man either
finds him unacceptable, or currently holds a man she strictly prefers to him. -/
def Inv (R : α → Finset β) : Prop :=
  ∀ a b, b ∈ R a →
    ¬ M.accM b a ∨ ∃ a'', M.holder R b = some a'' ∧ M.prefB b a < M.prefB b a''

theorem inv_empty : M.Inv (fun _ => ∅) := by
  intro a b hb; simp at hb

/-- The invariant is preserved by a deferred-acceptance round. -/
theorem inv_step (hA : ∀ a, Function.Injective (M.prefA a))
    (hB : ∀ b, Function.Injective (M.prefB b)) {R : α → Finset β}
    (hInv : M.Inv R) : M.Inv (M.daStep R) := by
  classical
  intro a b hb
  simp only [daStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  rcases hb with hb_old | ⟨htop, hne⟩
  · rcases hInv a b hb_old with hunacc | ⟨a'', hhold, hlt⟩
    · exact Or.inl hunacc
    · obtain ⟨a''', ha''', hle⟩ := M.holder_improve (hA a'') hhold
      exact Or.inr ⟨a''', ha''', lt_of_lt_of_le hlt hle⟩
  · by_cases hacc : M.accM b a
    · have ha_suit : a ∈ M.suitors R b := M.mem_suitors.mpr ⟨htop, hacc⟩
      obtain ⟨a₀, ha₀⟩ : ∃ a₀, M.holder R b = some a₀ :=
        Option.isSome_iff_exists.mp (M.holder_isSome_of_suitors ⟨a, ha_suit⟩)
      have ha₀_ne : a₀ ≠ a := fun he => hne (he ▸ ha₀)
      have hlt : M.prefB b a < M.prefB b a₀ :=
        lt_of_le_of_ne ((M.holder_spec ha₀).2 a ha_suit) (fun he => ha₀_ne (hB b he).symm)
      obtain ⟨a''', ha''', hle⟩ := M.holder_improve (hA a₀) ha₀
      exact Or.inr ⟨a''', ha''', lt_of_lt_of_le hlt hle⟩
    · exact Or.inl hacc

theorem inv_iterate (hA : ∀ a, Function.Injective (M.prefA a))
    (hB : ∀ b, Function.Injective (M.prefB b)) (n : ℕ) :
    M.Inv (M.daStep^[n] (fun _ => ∅)) := by
  induction n with
  | zero => exact M.inv_empty
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact M.inv_step hA hB ih

/-- Any fixed point satisfying the deferred-acceptance invariant has no blocking
pair. (Strict preferences are used only to establish the invariant, not here.) -/
theorem no_blocking {R : α → Finset β}
    (hR : M.daStep R = R) (hInv : M.Inv R) :
    ¬ ∃ a b, M.IsBlockingPair (fun a => M.topChoice R a) a b := by
  classical
  rintro ⟨a, b, hApref, hAnone, hBpref, hBnone⟩
  -- (1) `a` finds `b` acceptable.
  have haccW : M.accW a b := by
    cases hμa : M.topChoice R a with
    | none => exact le_of_lt (hAnone hμa)
    | some b' =>
        exact le_of_lt (lt_of_le_of_lt (M.fixedPoint_ir hR a b' hμa).1 (hApref b' hμa))
  -- (2) `b` has already rejected `a`.
  have hb_in : b ∈ R a := by
    by_contra hb_notin
    have hb_avail : b ∈ M.available R a := M.mem_available.mpr ⟨hb_notin, haccW⟩
    obtain ⟨b', hb'⟩ : ∃ b', M.topChoice R a = some b' := by
      unfold topChoice; rw [dif_pos ⟨b, hb_avail⟩]; exact ⟨_, rfl⟩
    have h1 := (M.topChoice_spec hb').2 b hb_avail
    have h2 := hApref b' hb'
    omega
  -- (3) but then `b` holds someone she prefers to `a` — contradicting the block.
  rcases hInv a b hb_in with hunacc | ⟨a'', hhold, hlt⟩
  · apply hunacc
    by_cases hbm : ∃ a', M.topChoice R a' = some b
    · obtain ⟨a', ha'⟩ := hbm
      exact le_of_lt (lt_of_le_of_lt (M.fixedPoint_ir hR a' b ha').2 (hBpref a' ha'))
    · exact le_of_lt (hBnone (not_exists.mp hbm))
  · have hmatch : M.topChoice R a'' = some b := (M.mem_suitors.mp (M.holder_spec hhold).1).1
    have := hBpref a'' hmatch
    omega

/-! ### The deferred-acceptance matching -/

/-- The rejection state at the deferred-acceptance fixed point (iterating the round
operator from `∅`). -/
noncomputable def daFixedPoint : α → Finset β :=
  M.daStep^[Classical.choose M.exists_daStep_iterate_fixed] (fun _ => ∅)

theorem daStep_daFixedPoint : M.daStep M.daFixedPoint = M.daFixedPoint :=
  Classical.choose_spec M.exists_daStep_iterate_fixed

/-- The matching produced by men-proposing deferred acceptance: each man is assigned
his top remaining choice at the fixed point. -/
noncomputable def daMatching : α → Option β := fun a => M.topChoice M.daFixedPoint a

set_option linter.unusedFintypeInType false in
/-- **The deferred-acceptance matching is stable.** -/
theorem daMatching_isStable (hA : ∀ a, Function.Injective (M.prefA a))
    (hB : ∀ b, Function.Injective (M.prefB b)) : M.IsStable M.daMatching :=
  ⟨M.fixedPoint_isMatching M.daStep_daFixedPoint,
    fun a b h => M.fixedPoint_ir M.daStep_daFixedPoint a b h,
    M.no_blocking M.daStep_daFixedPoint (M.inv_iterate hA hB _)⟩

set_option linter.unusedFintypeInType false in
/-- **Gale–Shapley: stable matchings exist.** Every finite two-sided market with
strict preferences admits a stable matching, produced by men-proposing deferred
acceptance. -/
theorem exists_stable (hA : ∀ a, Function.Injective (M.prefA a))
    (hB : ∀ b, Function.Injective (M.prefB b)) :
    ∃ μ : α → Option β, M.IsStable μ :=
  ⟨M.daMatching, M.daMatching_isStable hA hB⟩

/-! ### Man-optimality

Men-proposing deferred acceptance is *man-optimal*: every man is matched to a woman
he weakly prefers to his partner in **any** stable matching. The classical argument
is that no man is ever rejected by a woman who is *achievable* for him (paired with
him in some stable matching). Besides strict preferences, this needs that no man is
exactly indifferent between an acceptable woman and remaining single (`hAne`), so
that an achievable block is a *strict* block. -/

/-- Woman `b` is *achievable* for man `a` if some stable matching pairs them. -/
def IsAchievable (a : α) (b : β) : Prop :=
  ∃ μ : α → Option β, M.IsStable μ ∧ μ a = some b

/-- **Man-optimality invariant.** No woman who has rejected `a` is achievable for
him: deferred acceptance never discards a stable partner. -/
def MAchInv (R : α → Finset β) : Prop :=
  ∀ a b, b ∈ R a → ¬ M.IsAchievable a b

omit [Fintype α] [Fintype β] in
theorem machInv_empty : M.MAchInv (fun _ => ∅) := by
  intro a b hb; simp at hb

/-- The man-optimality invariant is preserved by a deferred-acceptance round. The
heart is a blocking-pair contradiction: if `b` rejects `a` in favour of the man `a'`
she holds, and `b` were achievable for `a` via a stable `μ'`, then `(a', b)` blocks
`μ'` — `a'` prefers `b` to his (achievable, hence still-available) `μ'`-partner, and
`b` prefers `a'` to her `μ'`-partner `a`. -/
theorem machInv_step (hA : ∀ a, Function.Injective (M.prefA a))
    (hB : ∀ b, Function.Injective (M.prefB b))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b) {R : α → Finset β}
    (hInv : M.MAchInv R) : M.MAchInv (M.daStep R) := by
  classical
  intro a b hb
  simp only [daStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  rcases hb with hb_old | ⟨htop, hne⟩
  · exact hInv a b hb_old
  · rintro ⟨μ', hstable, hμ'⟩
    by_cases hacc : M.accM b a
    · have ha_suit : a ∈ M.suitors R b := M.mem_suitors.mpr ⟨htop, hacc⟩
      obtain ⟨a', ha'⟩ : ∃ a', M.holder R b = some a' :=
        Option.isSome_iff_exists.mp (M.holder_isSome_of_suitors ⟨a, ha_suit⟩)
      have ha'_ne : a' ≠ a := fun he => hne (he ▸ ha')
      have hpref_a' : M.prefB b a < M.prefB b a' :=
        lt_of_le_of_ne ((M.holder_spec ha').2 a ha_suit) (fun he => ha'_ne (hB b he).symm)
      obtain ⟨htop_a', _⟩ := M.mem_suitors.mp (M.holder_spec ha').1
      apply hstable.2.2
      refine ⟨a', b, ?_, ?_, ?_, ?_⟩
      · intro b'' hb''
        have hb''_notin : b'' ∉ R a' := fun hin => hInv a' b'' hin ⟨μ', hstable, hb''⟩
        have hb''_avail : b'' ∈ M.available R a' :=
          M.mem_available.mpr ⟨hb''_notin, (hstable.2.1 a' b'' hb'').1⟩
        have hle : M.prefA a' b'' ≤ M.prefA a' b := (M.topChoice_spec htop_a').2 b'' hb''_avail
        have hbne : b'' ≠ b := fun he => ha'_ne (hstable.1 a' a b'' hb'' (he ▸ hμ'))
        exact lt_of_le_of_ne hle (fun he => hbne (hA a' he))
      · intro _
        exact lt_of_le_of_ne (M.accW_of_topChoice htop_a') (hAne a' b)
      · intro a'' ha''
        have hmatch : a'' = a := hstable.1 a'' a b ha'' hμ'
        rw [hmatch]; exact hpref_a'
      · intro hcon
        exact absurd hμ' (hcon a)
    · exact hacc (hstable.2.1 a b hμ').2

theorem machInv_iterate (hA : ∀ a, Function.Injective (M.prefA a))
    (hB : ∀ b, Function.Injective (M.prefB b))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b) (n : ℕ) :
    M.MAchInv (M.daStep^[n] (fun _ => ∅)) := by
  induction n with
  | zero => exact M.machInv_empty
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact M.machInv_step hA hB hAne ih

/-- **Gale–Shapley is man-optimal.** Under strict preferences, with no man exactly
indifferent between an acceptable woman and remaining single, every man's
deferred-acceptance partner is weakly preferred to his partner in *any* stable
matching: for any stable `μ'` pairing `a` with `b'`, `a`'s `daMatching` partner
exists and is `prefA`-at-least `b'`. -/
theorem daMatching_man_optimal (hA : ∀ a, Function.Injective (M.prefA a))
    (hB : ∀ b, Function.Injective (M.prefB b))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b)
    {μ' : α → Option β} (hμ'stable : M.IsStable μ') {a : α} {b' : β}
    (h : μ' a = some b') :
    ∃ b, M.daMatching a = some b ∧ M.prefA a b' ≤ M.prefA a b := by
  classical
  have hInv : M.MAchInv M.daFixedPoint := M.machInv_iterate hA hB hAne _
  have hb'_notin : b' ∉ M.daFixedPoint a := fun hin => hInv a b' hin ⟨μ', hμ'stable, h⟩
  have hb'_avail : b' ∈ M.available M.daFixedPoint a :=
    M.mem_available.mpr ⟨hb'_notin, (hμ'stable.2.1 a b' h).1⟩
  obtain ⟨b, hb⟩ : ∃ b, M.topChoice M.daFixedPoint a = some b := by
    unfold topChoice; rw [dif_pos ⟨b', hb'_avail⟩]; exact ⟨_, rfl⟩
  exact ⟨b, hb, (M.topChoice_spec hb).2 b' hb'_avail⟩

end MatchingMarket

end GameTheory
