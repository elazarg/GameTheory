/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSoloQuitterEquilibrium

/-!
# Two blockers cover the owner's rate interval

Fix an owner `i` in a quitting game (the setting of Solan and Vieille,
*Quitting games*, Israel J. Math. 2001) and let every other player continue
surely while `i` quits at rate `h ∈ (0,1]`.  Opponent `j` weakly prefers to
stay out of the exit exactly when its *joining gain*

`d_ij(h) = (1-h) * r_j({j}) + h * r_j({i,j}) - r_j({i})`

is nonpositive, so the owner's solo row is an equilibrium row at rate `h`
exactly when `d_ij(h) ≤ 0` for every `j ≠ i` -- this is
`QuittingSoloQuitterCriterion`, and each `d_ij` is affine in `h`.

This file settles the structure of the *failure* of that criterion at every
rate.

## The designation that fails

If no rate works one might hope to designate a single opponent responsible
for it: some `j` with `d_ij(h) > 0` for every `h ∈ (0,1]`.  That designation
is false.  `QuittingSwitchingBlockerTable` is a three-player table whose two
joining gains are `d_01(h) = h - 2/5` and `d_02(h) = 3/5 - h`.  Their
maximum is at least `1/10` at *every* real rate, so the obstruction is
uniform and not an endpoint artefact; yet the first opponent is content at
every `h ≤ 2/5` and the second at every `h ≥ 3/5`, so neither blocks all
rates.  `QuittingSwitchingBlockerTable.not_exists_universalJoiner` is the
machine-checked refutation.

## What is true: two blockers whose intervals overlap

`exists_universalRateBlocker_or_switchingPair` is the replacement.  For a
finite family of affine functions covering `(0,1]` by positivity, either

* some member is positive on all of `(0,1]` (a universal blocker), or
* two distinct members `a ≠ b` and reals `0 < β < α ≤ 1` exist with `f a`
  positive on `(0, α)` and `f b` positive on `(β, 1]`.

The two intervals overlap on `(β, α)`, so the pair alone already covers
`(0,1]` (`isUniversalRateBlocker_of_initial_of_terminal`): *two* blockers
always suffice, and the switch between them happens strictly inside the
interval.  The proof is the affine classification of the
positivity sets -- empty, everything, an initial interval, or a terminal
interval -- plus one maximisation over the initial intervals.

## The two branches are not exclusive

`exists_family_isUniversalRateBlocker_and_switchingPair` exhibits a
three-member family satisfying *both* branches, so the disjunction above
cannot be upgraded to an exclusive one with the branches as stated: the
sharp statement is `exists_switchingPair_of_forall_not_isUniversalRateBlocker`,
where the switching pair is produced from the failure of the universal
branch.

## The quitting interface

`exists_soloQuitterRate_or_universalJoiner_or_switchingPair` is the corrected
gate: either some rate in `(0,1]` certifies the owner's solo row, or some
opponent `j` satisfies the endpoint inequalities `r_j({i}) ≤ r_j({j})` and
`r_j({i}) < r_j({i,j})` -- which
`isUniversalRateBlocker_quittingJoiningGain_iff` shows is exactly what it
means to block every rate -- or two opponents split the interval between
them as above.
-/

noncomputable section

namespace GameTheory

/-! ## Affine functions of the owner's rate -/

/-- An affine function of the owner's quitting rate. -/
def IsRateAffine (f : ℝ → ℝ) : Prop :=
  ∃ slope intercept : ℝ, ∀ h : ℝ, f h = slope * h + intercept

/-- `f` is positive at every rate in `(0,1]`: a *universal blocker*. -/
def IsUniversalRateBlocker (f : ℝ → ℝ) : Prop :=
  ∀ h : ℝ, 0 < h → h ≤ 1 → 0 < f h

/-- `f` is positive at every rate in `(0, α)`: an *initial blocker*. -/
def IsInitialRateBlocker (f : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ h : ℝ, 0 < h → h < α → 0 < f h

/-- `f` is positive at every rate in `(β, 1]`: a *terminal blocker*. -/
def IsTerminalRateBlocker (f : ℝ → ℝ) (β : ℝ) : Prop :=
  ∀ h : ℝ, β < h → h ≤ 1 → 0 < f h

/-- An affine function is the interpolation of its two endpoint values. -/
theorem IsRateAffine.eq_endpoints {f : ℝ → ℝ} (hf : IsRateAffine f) (h : ℝ) :
    f h = (1 - h) * f 0 + h * f 1 := by
  obtain ⟨slope, intercept, hslope⟩ := hf
  simp only [hslope]
  ring

/-- An affine function nonpositive at both endpoints is nonpositive
throughout `[0,1]`. -/
theorem IsRateAffine.nonpos_of_endpoints_nonpos {f : ℝ → ℝ}
    (hf : IsRateAffine f) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hzero : f 0 ≤ 0) (hone : f 1 ≤ 0) : f h ≤ 0 := by
  rw [hf.eq_endpoints h]
  nlinarith

/-- An affine function that is strictly negative at rate zero is
nonpositive on a whole initial segment of rates. -/
theorem IsRateAffine.exists_pos_forall_nonpos_of_neg {f : ℝ → ℝ}
    (hf : IsRateAffine f) (hzero : f 0 < 0) :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ h : ℝ, 0 < h → h ≤ threshold → f h ≤ 0 := by
  obtain ⟨slope, intercept, hslope⟩ := hf
  have hintercept : intercept < 0 := by
    simpa [hslope] using hzero
  have hden : (0 : ℝ) < 1 + |slope| := by positivity
  refine ⟨(-intercept) / (1 + |slope|), div_pos (by linarith) hden, ?_⟩
  intro h hh0 hhthreshold
  have hslopeabs : slope * h ≤ |slope| * h := by
    nlinarith [le_abs_self slope]
  have hscaled : |slope| * h ≤ |slope| * ((-intercept) / (1 + |slope|)) :=
    mul_le_mul_of_nonneg_left hhthreshold (abs_nonneg slope)
  have hbound : |slope| * ((-intercept) / (1 + |slope|)) ≤ -intercept := by
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith [abs_nonneg slope]
  rw [hslope]
  linarith

/-- An affine function strictly negative at rate zero is not a universal
blocker: it is nonpositive at all sufficiently small admissible rates. -/
theorem IsRateAffine.not_isUniversalRateBlocker_of_neg {f : ℝ → ℝ}
    (hf : IsRateAffine f) (hzero : f 0 < 0) : ¬ IsUniversalRateBlocker f := by
  obtain ⟨threshold, hthreshold, hnonpos⟩ :=
    hf.exists_pos_forall_nonpos_of_neg hzero
  intro huniversal
  have hsmall : 0 < min threshold 1 := lt_min hthreshold one_pos
  have hpos := huniversal (min threshold 1) hsmall (min_le_right _ _)
  have hnp := hnonpos (min threshold 1) hsmall (min_le_left _ _)
  linarith

/-- An affine non-blocker that is nonpositive at rate zero is nonpositive on
a whole initial segment of rates.  Both hypotheses are needed: the function
`h ↦ h` vanishes at zero and blocks every admissible rate. -/
theorem IsRateAffine.exists_pos_forall_nonpos_of_nonpos {f : ℝ → ℝ}
    (hf : IsRateAffine f) (hzero : f 0 ≤ 0)
    (hnot : ¬ IsUniversalRateBlocker f) :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ h : ℝ, 0 < h → h ≤ threshold → f h ≤ 0 := by
  rcases lt_or_eq_of_le hzero with hneg | heq
  · exact hf.exists_pos_forall_nonpos_of_neg hneg
  · obtain ⟨slope, intercept, hslope⟩ := hf
    have hintercept : intercept = 0 := by
      simpa [hslope] using heq
    have hslopenonpos : slope ≤ 0 := by
      by_contra hcontra
      push Not at hcontra
      exact hnot fun h hh0 _ => by
        rw [hslope, hintercept]
        positivity
    refine ⟨1, one_pos, fun h hh0 _ => ?_⟩
    rw [hslope, hintercept]
    nlinarith

/-- **Initial-interval classification.**  An affine non-blocker that is
positive at rate zero is positive exactly on `(-∞, α)` for a single
`α ∈ (0,1]`. -/
theorem IsRateAffine.exists_initial_of_pos {f : ℝ → ℝ} (hf : IsRateAffine f)
    (hzero : 0 < f 0) (hnot : ¬ IsUniversalRateBlocker f) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ h : ℝ, 0 < f h ↔ h < α := by
  have hone : f 1 ≤ 0 := by
    by_contra hcontra
    push Not at hcontra
    refine hnot fun h hh0 hh1 => ?_
    rw [hf.eq_endpoints h]
    nlinarith
  have hslope : 0 < f 0 - f 1 := by linarith
  refine ⟨f 0 / (f 0 - f 1), div_pos hzero hslope,
    (div_le_one hslope).mpr (by linarith), fun h => ?_⟩
  have hexpand : (1 - h) * f 0 + h * f 1 = f 0 - h * (f 0 - f 1) := by ring
  rw [hf.eq_endpoints h, hexpand, lt_div_iff₀ hslope]
  constructor
  · intro hpos
    linarith
  · intro hlt
    linarith

/-- **Terminal-interval classification.**  An affine non-blocker that is
nonpositive at rate zero but positive somewhere in `(0,1]` is positive
exactly on `(β, ∞)` for a single `β ∈ (0,1)`. -/
theorem IsRateAffine.exists_terminal_of_nonpos {f : ℝ → ℝ}
    (hf : IsRateAffine f) (hzero : f 0 ≤ 0)
    (hsome : ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < f h)
    (hnot : ¬ IsUniversalRateBlocker f) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ h : ℝ, 0 < f h ↔ β < h := by
  obtain ⟨witness, hwitness0, hwitness1, hwitnesspos⟩ := hsome
  have hone : 0 < f 1 := by
    by_contra hcontra
    push Not at hcontra
    have := hf.nonpos_of_endpoints_nonpos hwitness0.le hwitness1 hzero hcontra
    linarith
  have hneg : f 0 < 0 := by
    rcases lt_or_eq_of_le hzero with hlt | heq
    · exact hlt
    · refine absurd (fun h hh0 _ => ?_) hnot
      rw [hf.eq_endpoints h, heq]
      nlinarith [mul_pos hh0 hone]
  have hslope : 0 < f 1 - f 0 := by linarith
  refine ⟨(-f 0) / (f 1 - f 0), div_pos (by linarith) hslope,
    (div_lt_one hslope).mpr (by linarith), fun h => ?_⟩
  have hexpand : (1 - h) * f 0 + h * f 1 = f 0 + h * (f 1 - f 0) := by ring
  rw [hf.eq_endpoints h, hexpand, div_lt_iff₀ hslope]
  constructor
  · intro hpos
    linarith
  · intro hlt
    linarith

/-! ## The two-blocker interval cover -/

/-- **The two-blocker interval cover, sharp form.**  Let a finite family of
affine functions cover `(0,1]`, in the sense that at every rate some member
is positive, and let no single member be positive on all of `(0,1]`.  Then
two *distinct* members already cover the interval, one on an initial segment
`(0, α)` and one on a terminal segment `(β, 1]`, with `0 < β < α ≤ 1`: the
two segments overlap, and the switch happens strictly inside `(0,1]`.

Distinctness is automatic rather than assumed: a single function positive on
`(0, α)` and on `(β, 1]` with `β < α` is positive on all of `(0,1]`, which
the hypothesis excludes. -/
theorem exists_switchingPair_of_forall_not_isUniversalRateBlocker
    {J : Type*} (index : Finset J) (f : J → ℝ → ℝ)
    (haffine : ∀ j ∈ index, IsRateAffine (f j))
    (hcover : ∀ h : ℝ, 0 < h → h ≤ 1 → ∃ j ∈ index, 0 < f j h)
    (hnot : ∀ j ∈ index, ¬ IsUniversalRateBlocker (f j)) :
    ∃ a ∈ index, ∃ b ∈ index, a ≠ b ∧ ∃ α β : ℝ,
      0 < β ∧ β < α ∧ α ≤ 1 ∧
        IsInitialRateBlocker (f a) α ∧ IsTerminalRateBlocker (f b) β := by
  classical
  have hnonempty : index.Nonempty := by
    obtain ⟨j, hj, _⟩ := hcover 1 one_pos le_rfl
    exact ⟨j, hj⟩
  -- Some member is positive at rate zero: otherwise all members are
  -- nonpositive on a common initial segment, which is then uncovered.
  have hpositiveAtZero : ∃ j ∈ index, 0 < f j 0 := by
    by_contra hnone
    push Not at hnone
    have hthresholds : ∀ j ∈ index, ∃ threshold : ℝ, 0 < threshold ∧
        ∀ h : ℝ, 0 < h → h ≤ threshold → f j h ≤ 0 := fun j hj =>
      (haffine j hj).exists_pos_forall_nonpos_of_nonpos (hnone j hj) (hnot j hj)
    choose! threshold hthresholdPos hthresholdNonpos using hthresholds
    obtain ⟨least, hleastMem, hleastMin⟩ :=
      index.exists_min_image threshold hnonempty
    have hsmall : 0 < min (threshold least) 1 :=
      lt_min (hthresholdPos least hleastMem) one_pos
    obtain ⟨j, hj, hjpos⟩ :=
      hcover (min (threshold least) 1) hsmall (min_le_right _ _)
    have hjnonpos := hthresholdNonpos j hj (min (threshold least) 1) hsmall
      (le_trans (min_le_left _ _) (hleastMin j hj))
    linarith
  -- Every member positive at rate zero owns an initial interval.
  have hinitials : ∀ j ∈ index, 0 < f j 0 →
      ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ h : ℝ, 0 < f j h ↔ h < α := fun j hj hjpos =>
    (haffine j hj).exists_initial_of_pos hjpos (hnot j hj)
  choose! endpoint hendpointPos hendpointLe hendpointIff using hinitials
  -- Take the initial interval with the largest endpoint.
  obtain ⟨a, hamem, hamax⟩ :=
    (index.filter fun j => 0 < f j 0).exists_max_image endpoint <| by
      obtain ⟨j, hj, hjpos⟩ := hpositiveAtZero
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, hjpos⟩⟩
  obtain ⟨haindex, hapos⟩ := Finset.mem_filter.mp hamem
  have haPos : 0 < endpoint a := hendpointPos a haindex hapos
  have haLe : endpoint a ≤ 1 := hendpointLe a haindex hapos
  -- At the largest initial endpoint the cover must be supplied by a member
  -- that is nonpositive at rate zero, hence by a terminal interval.
  obtain ⟨b, hbindex, hbpos⟩ := hcover (endpoint a) haPos haLe
  have hbzero : f b 0 ≤ 0 := by
    by_contra hcontra
    push Not at hcontra
    have hbmem : b ∈ index.filter fun j => 0 < f j 0 :=
      Finset.mem_filter.mpr ⟨hbindex, hcontra⟩
    have hble := hamax b hbmem
    have hblt := (hendpointIff b hbindex hcontra (endpoint a)).mp hbpos
    linarith
  obtain ⟨β, hβpos, hβlt1, hβiff⟩ := (haffine b hbindex).exists_terminal_of_nonpos
    hbzero ⟨endpoint a, haPos, haLe, hbpos⟩ (hnot b hbindex)
  refine ⟨a, haindex, b, hbindex, ?_, endpoint a, β, hβpos,
    (hβiff (endpoint a)).mp hbpos, haLe, fun h hh0 hhα => ?_,
    fun h hβh _ => (hβiff h).mpr hβh⟩
  · rintro rfl
    linarith
  · exact (hendpointIff a haindex hapos h).mpr hhα

/-- **The two-blocker interval cover.**  A finite family of affine functions
whose positivity sets cover `(0,1]` contains either a single member positive
on all of `(0,1]`, or a pair of distinct members splitting the interval into
an overlapping initial part `(0, α)` and terminal part `(β, 1]` with
`0 < β < α ≤ 1`.

The disjunction is not exclusive as stated -- see
`exists_family_isUniversalRateBlocker_and_switchingPair` -- the exclusive
reading is `exists_switchingPair_of_forall_not_isUniversalRateBlocker`, whose
second branch is derived from the failure of the first. -/
theorem exists_universalRateBlocker_or_switchingPair
    {J : Type*} (index : Finset J) (f : J → ℝ → ℝ)
    (haffine : ∀ j ∈ index, IsRateAffine (f j))
    (hcover : ∀ h : ℝ, 0 < h → h ≤ 1 → ∃ j ∈ index, 0 < f j h) :
    (∃ j ∈ index, IsUniversalRateBlocker (f j)) ∨
      ∃ a ∈ index, ∃ b ∈ index, a ≠ b ∧ ∃ α β : ℝ,
        0 < β ∧ β < α ∧ α ≤ 1 ∧
          IsInitialRateBlocker (f a) α ∧ IsTerminalRateBlocker (f b) β := by
  by_cases huniversal : ∃ j ∈ index, IsUniversalRateBlocker (f j)
  · exact Or.inl huniversal
  · push Not at huniversal
    exact Or.inr (exists_switchingPair_of_forall_not_isUniversalRateBlocker
      index f haffine hcover huniversal)

/-- A switching pair does cover the whole interval: at every rate in `(0,1]`
one of the two blockers is positive.  This is the sense in which *two*
blockers always suffice. -/
theorem isUniversalRateBlocker_of_initial_of_terminal {fa fb : ℝ → ℝ}
    {α β : ℝ} (hα : IsInitialRateBlocker fa α)
    (hβ : IsTerminalRateBlocker fb β) (h : ℝ) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hβα : β < α) : 0 < fa h ∨ 0 < fb h := by
  by_cases hlt : h < α
  · exact Or.inl (hα h hh0 hlt)
  · exact Or.inr (hβ h (lt_of_lt_of_le hβα (not_lt.mp hlt)) hh1)

/-- A universal blocker satisfies the switching-pair pattern by itself, with
`a = b`: it is an initial blocker at `α = 1` and a terminal blocker at
`β = 1/2`.  So the two blocking patterns are not exclusive even for a single
function; requiring the two indices to be distinct does not separate them
either, as `exists_family_isUniversalRateBlocker_and_switchingPair` shows. -/
theorem exists_initial_and_terminal_of_isUniversalRateBlocker {f : ℝ → ℝ}
    (hf : IsUniversalRateBlocker f) :
    ∃ α β : ℝ, 0 < β ∧ β < α ∧ α ≤ 1 ∧
      IsInitialRateBlocker f α ∧ IsTerminalRateBlocker f β :=
  ⟨1, 1 / 2, by norm_num, by norm_num, le_rfl,
    fun h hh0 hhα => hf h hh0 hhα.le,
    fun h hβh hh1 => hf h (by linarith) hh1⟩

/-- **The two branches are not mutually exclusive.**  The three-member
family `1`, `1 - h`, `2h - 1` on `(0,1]` has a universal blocker (the
constant `1`) *and* a switching pair of distinct indices (`1 - h` on
`(0,1)` together with `2h - 1` on `(1/2, 1]`).  So
`exists_universalRateBlocker_or_switchingPair` cannot be strengthened to an
exclusive disjunction with these branches, whatever the proof: the
conclusion is a genuine "or", and the sharp statement must carry the
negation of the first branch in the second, as
`exists_switchingPair_of_forall_not_isUniversalRateBlocker` does. -/
theorem exists_family_isUniversalRateBlocker_and_switchingPair :
    ∃ (index : Finset (Fin 3)) (f : Fin 3 → ℝ → ℝ),
      (∀ j ∈ index, IsRateAffine (f j)) ∧
      (∀ h : ℝ, 0 < h → h ≤ 1 → ∃ j ∈ index, 0 < f j h) ∧
      (∃ j ∈ index, IsUniversalRateBlocker (f j)) ∧
      (∃ a ∈ index, ∃ b ∈ index, a ≠ b ∧ ∃ α β : ℝ,
        0 < β ∧ β < α ∧ α ≤ 1 ∧
          IsInitialRateBlocker (f a) α ∧ IsTerminalRateBlocker (f b) β) := by
  have hzeroOne : (0 : Fin 3) ≠ 1 := by decide
  have hzeroTwo : (0 : Fin 3) ≠ 2 := by decide
  have honeTwo : (1 : Fin 3) ≠ 2 := by decide
  have htwoOne : (2 : Fin 3) ≠ 1 := by decide
  refine ⟨Finset.univ, fun j h =>
      (if j = 1 then -1 else if j = 2 then 2 else 0) * h +
        (if j = 2 then -1 else 1),
    fun j _ => ⟨_, _, fun h => rfl⟩, ?_, ?_, ?_⟩
  · intro h _ _
    exact ⟨0, Finset.mem_univ 0, by norm_num [hzeroOne, hzeroTwo]⟩
  · exact ⟨0, Finset.mem_univ 0,
      fun h _ _ => by norm_num [hzeroOne, hzeroTwo]⟩
  · refine ⟨1, Finset.mem_univ 1, 2, Finset.mem_univ 2, honeTwo,
      1, 1 / 2, by norm_num, by norm_num, le_rfl, fun h _ hh => ?_,
      fun h hh _ => ?_⟩
    · norm_num [honeTwo]
      linarith
    · norm_num [htwoOne]
      linarith

/-! ## The joining gain of one opponent -/

section JoiningGain

variable {ι : Type} [DecidableEq ι]

/-- The *joining gain* of `other` against the owner's solo exit at rate `h`:
what `other` gains by quitting -- alone with probability `1 - h`, together
with `owner` with probability `h` -- over letting `owner` quit alone.  The
owner's solo row is an equilibrium row at rate `h` exactly when every
opponent's joining gain is nonpositive. -/
def quittingJoiningGain (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner other : ι) (h : ℝ) : ℝ :=
  (1 - h) * quittingSoloReward reward other other +
    h * quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward owner other

/-- The joining gain is affine in the owner's rate. -/
theorem isRateAffine_quittingJoiningGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner other : ι) :
    IsRateAffine (quittingJoiningGain reward owner other) :=
  ⟨quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other,
    quittingSoloReward reward other other -
      quittingSoloReward reward owner other,
    fun h => by unfold quittingJoiningGain; ring⟩

/-- At rate zero the joining gain compares the opponent's own solo exit with
the owner's solo absorption payoff. -/
@[simp] theorem quittingJoiningGain_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner other : ι) :
    quittingJoiningGain reward owner other 0 =
      quittingSoloReward reward other other -
        quittingSoloReward reward owner other := by
  unfold quittingJoiningGain
  ring

/-- At the sure-quit rate the joining gain compares the collision payoff with
the owner's solo absorption payoff. -/
@[simp] theorem quittingJoiningGain_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner other : ι) :
    quittingJoiningGain reward owner other 1 =
      quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward owner other := by
  unfold quittingJoiningGain
  ring

/-- The solo-quitter criterion at rate `p` is the nonpositivity of every
opponent's joining gain. -/
theorem quittingSoloQuitterCriterion_iff_forall_joiningGain_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) (p : ℝ) :
    QuittingSoloQuitterCriterion reward owner p ↔
      ∀ other, other ≠ owner →
        quittingJoiningGain reward owner other p ≤ 0 := by
  unfold QuittingSoloQuitterCriterion quittingJoiningGain
  constructor
  · intro hcriterion other hother
    linarith [hcriterion other hother]
  · intro hgain other hother
    linarith [hgain other hother]

/-- The joining obstruction at rate `p` is the existence of an opponent with
strictly positive joining gain. -/
theorem quittingSoloJoiningObstruction_iff_exists_joiningGain_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) (p : ℝ) :
    QuittingSoloJoiningObstruction reward owner p ↔
      ∃ other, other ≠ owner ∧
        0 < quittingJoiningGain reward owner other p := by
  unfold QuittingSoloJoiningObstruction quittingJoiningGain
  constructor
  · rintro ⟨other, hother, hlt⟩
    exact ⟨other, hother, by linarith⟩
  · rintro ⟨other, hother, hlt⟩
    exact ⟨other, hother, by linarith⟩

/-- **Endpoint characterisation of a universal joiner.**  An opponent blocks
*every* owner rate in `(0,1]` exactly when it weakly prefers its own solo
exit to the owner's solo absorption payoff and strictly prefers the
collision to it:

`r_j({i}) ≤ r_j({j})` and `r_j({i}) < r_j({i,j})`.

The first inequality may be weak because the joining gain at rate zero is a
limit of admissible rates, the second is strict because rate one is itself
admissible. -/
theorem isUniversalRateBlocker_quittingJoiningGain_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner other : ι) :
    IsUniversalRateBlocker (quittingJoiningGain reward owner other) ↔
      quittingSoloReward reward owner other ≤
          quittingSoloReward reward other other ∧
        quittingSoloReward reward owner other <
          quittingSingletonCollisionReward reward owner other := by
  constructor
  · intro huniversal
    have hone := huniversal 1 one_pos le_rfl
    rw [quittingJoiningGain_one] at hone
    refine ⟨?_, by linarith⟩
    by_contra hcontra
    push Not at hcontra
    refine (isRateAffine_quittingJoiningGain reward owner
      other).not_isUniversalRateBlocker_of_neg ?_ huniversal
    rw [quittingJoiningGain_zero]
    linarith
  · rintro ⟨hzero, hone⟩ h hh0 hh1
    rw [(isRateAffine_quittingJoiningGain reward owner other).eq_endpoints h,
      quittingJoiningGain_zero, quittingJoiningGain_one]
    nlinarith

end JoiningGain

/-! ## The corrected gate at the quitting interface -/

section QuittingInterface

variable {ι : Type} [Finite ι] [DecidableEq ι]

/-- **The corrected designation.**  If the owner's solo row fails at every
rate in `(0,1]`, then either some opponent blocks every rate -- equivalently,
by `isUniversalRateBlocker_quittingJoiningGain_iff`, satisfies
`r_j({i}) ≤ r_j({j})` and `r_j({i}) < r_j({i,j})` -- or two *distinct*
opponents split the interval, one blocking `(0, α)` and the other `(β, 1]`
with `0 < β < α ≤ 1`.

The second branch is not hypothetical: `QuittingSwitchingBlockerTable` is a
three-player table realising it, with no universal joiner at all. -/
theorem exists_universalJoiner_or_switchingPair_of_universalJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hobstruction : ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward owner p) :
    (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other ≤
            quittingSoloReward reward other other ∧
          quittingSoloReward reward owner other <
            quittingSingletonCollisionReward reward owner other) ∨
      ∃ a, a ≠ owner ∧ ∃ b, b ≠ owner ∧ a ≠ b ∧ ∃ α β : ℝ,
        0 < β ∧ β < α ∧ α ≤ 1 ∧
          IsInitialRateBlocker (quittingJoiningGain reward owner a) α ∧
          IsTerminalRateBlocker (quittingJoiningGain reward owner b) β := by
  letI := Fintype.ofFinite ι
  have hcover : ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ j ∈ Finset.univ.erase owner,
        0 < quittingJoiningGain reward owner j h := by
    intro h hh0 hh1
    obtain ⟨other, hother, hlt⟩ :=
      (quittingSoloJoiningObstruction_iff_exists_joiningGain_pos reward owner
        h).mp (hobstruction h hh0 hh1)
    exact ⟨other, Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩, hlt⟩
  rcases exists_universalRateBlocker_or_switchingPair (Finset.univ.erase owner)
    (fun j => quittingJoiningGain reward owner j)
    (fun j _ => isRateAffine_quittingJoiningGain reward owner j) hcover with
    ⟨j, hj, huniversal⟩ | ⟨a, ha, b, hb, hab, α, β, hβ, hβα, hα, hinit, hterm⟩
  · exact Or.inl ⟨j, (Finset.mem_erase.mp hj).1,
      (isUniversalRateBlocker_quittingJoiningGain_iff reward owner j).mp
        huniversal⟩
  · exact Or.inr ⟨a, (Finset.mem_erase.mp ha).1, b,
      (Finset.mem_erase.mp hb).1, hab, α, β, hβ, hβα, hα, hinit, hterm⟩

/-- **The corrected gate.**  Either some rate in `(0,1]` certifies the
owner's solo row -- the hypothesis of
`soloStationaryRoot_isAbsorbingEquilibriumRow_of_rate` -- or some opponent
blocks every rate, or two distinct opponents split the interval between an
initial and a terminal blocking segment that overlap. -/
theorem exists_soloQuitterRate_or_universalJoiner_or_switchingPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    (∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ QuittingSoloQuitterCriterion reward owner p) ∨
      (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other ≤
            quittingSoloReward reward other other ∧
          quittingSoloReward reward owner other <
            quittingSingletonCollisionReward reward owner other) ∨
      ∃ a, a ≠ owner ∧ ∃ b, b ≠ owner ∧ a ≠ b ∧ ∃ α β : ℝ,
        0 < β ∧ β < α ∧ α ≤ 1 ∧
          IsInitialRateBlocker (quittingJoiningGain reward owner a) α ∧
          IsTerminalRateBlocker (quittingJoiningGain reward owner b) β := by
  rcases exists_soloQuitterRate_or_universalJoining reward owner with
    hrate | hobstruction
  · exact Or.inl hrate
  · exact Or.inr (exists_universalJoiner_or_switchingPair_of_universalJoining
      reward owner hobstruction)

/-- **With at most two players the single-blocker designation is correct.**
The switching branch needs two *distinct* opponents of the owner, hence at
least three players; below that the gate collapses to the dichotomy "some
rate works, or one opponent blocks every rate".  Three players is therefore
exactly where the designation starts to fail, and
`QuittingSwitchingBlockerTable` realises that failure. -/
theorem exists_soloQuitterRate_or_universalJoiner_of_card_le_two
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hcard : Nat.card ι ≤ 2) :
    (∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ QuittingSoloQuitterCriterion reward owner p) ∨
      ∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other ≤
            quittingSoloReward reward other other ∧
          quittingSoloReward reward owner other <
            quittingSingletonCollisionReward reward owner other := by
  letI := Fintype.ofFinite ι
  rcases exists_soloQuitterRate_or_universalJoiner_or_switchingPair reward
    owner with hrate | hjoiner | ⟨a, hane, b, hbne, hab, _⟩
  · exact Or.inl hrate
  · exact Or.inr hjoiner
  · exfalso
    have hthree : ({owner, a, b} : Finset ι).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hane, Ne.symm hbne]),
        Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    have hle : ({owner, a, b} : Finset ι).card ≤ Fintype.card ι :=
      Finset.card_le_univ _
    rw [hthree, ← Nat.card_eq_fintype_card] at hle
    omega

end QuittingInterface

/-! ## The three-player table refuting the single-blocker designation -/

namespace QuittingSwitchingBlockerTable

/-- A three-player quitting table with owner `0`.  Player `1` collects `1`
when `0` and `1` quit together, `2/5` when `0` quits without `1`, and `0`
otherwise; player `2` collects `0` when `0` and `2` quit together, `2/5`
when `0` quits without `2`, `1` when `2` quits without `0`, and `0`
otherwise; player `0` always collects `0`.

The six entries this pins down (see `reward_entries`) are

`r_1({1}) = 0`, `r_1({0}) = 2/5`, `r_1({0,1}) = 1`,
`r_2({2}) = 1`, `r_2({0}) = 2/5`, `r_2({0,2}) = 0`,

and they make the two joining gains against the owner's solo exit
`d_01(h) = h - 2/5` and `d_02(h) = 3/5 - h`. -/
def reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3) := fun S who =>
  if who = 1 then
    (if (0 : Fin 3) ∈ S.val then (if (1 : Fin 3) ∈ S.val then 1 else 2 / 5)
      else 0)
  else if who = 2 then
    (if (0 : Fin 3) ∈ S.val then (if (2 : Fin 3) ∈ S.val then 0 else 2 / 5)
      else if (2 : Fin 3) ∈ S.val then 1 else 0)
  else 0

/-- **The declared entries.**  The six entries the two joining gains depend
on are exactly the ones named in the definition's docstring. -/
theorem reward_entries :
    quittingSoloReward reward 1 1 = 0 ∧
      quittingSoloReward reward 0 1 = 2 / 5 ∧
        quittingSingletonCollisionReward reward 0 1 = 1 ∧
          quittingSoloReward reward 2 2 = 1 ∧
            quittingSoloReward reward 0 2 = 2 / 5 ∧
              quittingSingletonCollisionReward reward 0 2 = 0 := by
  have hzeroOne : (0 : Fin 3) ≠ 1 := by decide
  have hzeroTwo : (0 : Fin 3) ≠ 2 := by decide
  have honeZero : (1 : Fin 3) ≠ 0 := by decide
  have honeTwo : (1 : Fin 3) ≠ 2 := by decide
  have htwoZero : (2 : Fin 3) ≠ 0 := by decide
  have htwoOne : (2 : Fin 3) ≠ 1 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward,
      hzeroOne, hzeroTwo, honeZero, honeTwo, htwoZero, htwoOne]

/-- The first opponent's joining gain is `h ↦ h - 2/5`: it is content with
every rate at most `2/5`. -/
theorem quittingJoiningGain_one_eq (h : ℝ) :
    quittingJoiningGain reward 0 1 h = h - 2 / 5 := by
  obtain ⟨hsolo, hownerSolo, hcollision, -, -, -⟩ := reward_entries
  unfold quittingJoiningGain
  rw [hsolo, hownerSolo, hcollision]
  ring

/-- The second opponent's joining gain is `h ↦ 3/5 - h`: it is content with
every rate at least `3/5`. -/
theorem quittingJoiningGain_two_eq (h : ℝ) :
    quittingJoiningGain reward 0 2 h = 3 / 5 - h := by
  obtain ⟨-, -, -, hsolo, hownerSolo, hcollision⟩ := reward_entries
  unfold quittingJoiningGain
  rw [hsolo, hownerSolo, hcollision]
  ring

/-- **The obstruction is uniform.**  At every real rate some opponent's
joining gain is at least `1/10`; the two gains sum to `1/5`, so the bound is
attained at `h = 1/2` and the failure is nowhere marginal.  In particular it
is not an endpoint pathology of `(0,1]`. -/
theorem exists_joiningGain_margin (h : ℝ) :
    ∃ other : Fin 3, other ≠ 0 ∧
      1 / 10 ≤ quittingJoiningGain reward 0 other h := by
  by_cases hhalf : h ≤ 1 / 2
  · refine ⟨2, by decide, ?_⟩
    rw [quittingJoiningGain_two_eq]
    linarith
  · refine ⟨1, by decide, ?_⟩
    rw [quittingJoiningGain_one_eq]
    linarith [not_le.mp hhalf]

/-- **Every owner rate fails.**  The owner's solo row is obstructed at every
rate -- not merely at every admissible rate in `(0,1]`. -/
theorem forall_quittingSoloJoiningObstruction (p : ℝ) :
    QuittingSoloJoiningObstruction reward 0 p := by
  obtain ⟨other, hother, hmargin⟩ := exists_joiningGain_margin p
  exact (quittingSoloJoiningObstruction_iff_exists_joiningGain_pos reward 0
    p).mpr ⟨other, hother, by linarith⟩

/-- **No rate certifies the owner's solo row.** -/
theorem not_quittingSoloQuitterCriterion (p : ℝ) :
    ¬ QuittingSoloQuitterCriterion reward 0 p := fun hcriterion =>
  (quittingSoloQuitterCriterion_iff_not_joiningObstruction reward 0 p).mp
    hcriterion (forall_quittingSoloJoiningObstruction p)

/-- **The refutation.**  Although every owner rate is obstructed, no single
opponent is responsible: each opponent is content at some admissible rate.
This refutes the designation of a single universal joiner. -/
theorem not_exists_universalJoiner :
    (∀ p : ℝ, 0 < p → p ≤ 1 →
        QuittingSoloJoiningObstruction reward 0 p) ∧
      ¬ ∃ other : Fin 3, other ≠ 0 ∧
        IsUniversalRateBlocker (quittingJoiningGain reward 0 other) := by
  refine ⟨fun p _ _ => forall_quittingSoloJoiningObstruction p, ?_⟩
  rintro ⟨other, hother, huniversal⟩
  have hcases : other = 1 ∨ other = 2 := by
    clear huniversal
    revert hother
    revert other
    decide
  rcases hcases with rfl | rfl
  · have hcontent := huniversal (2 / 5) (by norm_num) (by norm_num)
    rw [quittingJoiningGain_one_eq] at hcontent
    linarith
  · have hcontent := huniversal 1 one_pos le_rfl
    rw [quittingJoiningGain_two_eq] at hcontent
    linarith

/-- **The switching pair.**  The second opponent blocks the initial segment
`(0, 3/5)` and the first blocks the terminal segment `(2/5, 1]`; the two
overlap on `(2/5, 3/5)`.  This is the second branch of
`exists_soloQuitterRate_or_universalJoiner_or_switchingPair`, realised. -/
theorem isSwitchingPair :
    IsInitialRateBlocker (quittingJoiningGain reward 0 2) (3 / 5) ∧
      IsTerminalRateBlocker (quittingJoiningGain reward 0 1) (2 / 5) := by
  constructor
  · intro h _ hlt
    rw [quittingJoiningGain_two_eq]
    linarith
  · intro h hlt _
    rw [quittingJoiningGain_one_eq]
    linarith

end QuittingSwitchingBlockerTable

end GameTheory
