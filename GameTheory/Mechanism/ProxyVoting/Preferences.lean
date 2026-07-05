/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting.Bounded
import GameTheory.Mechanism.ProxyVoting.PartialInformation

/-!
# Preference-parametric proxy voting

This file adds an exact-preference layer for strategic proxy voting.  The
existing development uses two concrete readings of preference:

* Euclidean distance from a peak (`Prefers`);
* forced single-peaked comparisons (`SPPrefers`/`SPWeaklyPrefers`).

The definitions below parameterize better responses, truth-orientation, and
dominating manipulations by arbitrary strict and weak outcome preferences.
Compatibility hypotheses connect those preferences to single-peaked geometry,
so the geometric theorems in the rest of the development can be reused without
identifying all single-peaked preferences with Euclidean distance.  For
meta-moves, adding ordinary strict transitivity also recovers the fixed-agent
reading of the paper: terminal strict progress needs only the terminal
no-mirror-tie hypothesis, not the peak-separation hypothesis required by the
preference-free better-response class.
-/

namespace GameTheory

namespace ProxyVoting

variable {P F : Type*} [Fintype P] [Nonempty P] [LinearOrder P] [Fintype F]
variable {pp : P → ℝ} {q : F → ℝ} {s : P → ℝ}

/-! ## Preference compatibility -/

/-- A strict outcome preference for each proxy.  `spref j x y` means proxy
`j` strictly prefers outcome `x` to outcome `y`. -/
abbrev StrictOutcomePref (P : Type*) := P → ℝ → ℝ → Prop

/-- A weak outcome preference for each proxy. -/
abbrev WeakOutcomePref (P : Type*) := P → ℝ → ℝ → Prop

/-- Strict preferences are irreflexive. -/
def StrictPrefIrrefl (spref : StrictOutcomePref P) : Prop :=
  ∀ j x, ¬ spref j x x

/-- A strict preference respects single-peakedness at the proxy peaks: it never
strictly ranks an outcome above another outcome when single-peakedness forces
the reverse strict comparison. -/
def StrictPrefRespectsSinglePeaked (pp : P → ℝ) (spref : StrictOutcomePref P) :
    Prop :=
  ∀ j {x y}, spref j x y → ¬ SPPrefers (pp j) y x

/-- A strict preference extends the forced strict single-peaked comparisons. -/
def StrictPrefExtendsSinglePeaked (pp : P → ℝ) (spref : StrictOutcomePref P) :
    Prop :=
  ∀ j {x y}, SPPrefers (pp j) x y → spref j x y

/-- A weak preference extends the forced weak single-peaked comparisons. -/
def WeakPrefExtendsSinglePeaked (pp : P → ℝ) (wpref : WeakOutcomePref P) :
    Prop :=
  ∀ j {x y}, SPWeaklyPrefers (pp j) x y → wpref j x y

/-- Strict preference implies weak preference. -/
def StrictPrefImpliesWeak (spref : StrictOutcomePref P) (wpref : WeakOutcomePref P) :
    Prop :=
  ∀ j {x y}, spref j x y → wpref j x y

/-- Strict transitivity of outcome preferences. -/
def StrictPrefTrans (spref : StrictOutcomePref P) : Prop :=
  ∀ j {x y z}, spref j x y → spref j y z → spref j x z

/-- Weak-then-strict transitivity, the only transitivity law needed to turn a
forced weak-best comparison plus an exact better response into an exact
truthful better response. -/
def WeakStrictPrefTrans (spref : StrictOutcomePref P) (wpref : WeakOutcomePref P) :
    Prop :=
  ∀ j {x y z}, wpref j x y → spref j y z → spref j x z

/-- Euclidean strict preference, as used by the older concrete layer. -/
def euclideanStrictPref (pp : P → ℝ) : StrictOutcomePref P :=
  fun j x y => Prefers pp j x y

/-- Euclidean weak preference. -/
def euclideanWeakPref (pp : P → ℝ) : WeakOutcomePref P :=
  fun j x y => |x - pp j| ≤ |y - pp j|

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem euclideanStrictPref_irrefl (pp : P → ℝ) :
    StrictPrefIrrefl (euclideanStrictPref pp) := by
  intro j x h
  exact absurd h (lt_irrefl _)

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem euclideanStrictPref_respectsSinglePeaked (pp : P → ℝ) :
    StrictPrefRespectsSinglePeaked pp (euclideanStrictPref pp) := by
  intro j x y h hsp
  unfold euclideanStrictPref Prefers at h
  have hrev := hsp.abs_lt
  linarith

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem euclideanStrictPref_extendsSinglePeaked (pp : P → ℝ) :
    StrictPrefExtendsSinglePeaked pp (euclideanStrictPref pp) := by
  intro j x y h
  exact h.abs_lt

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem euclideanWeakPref_extendsSinglePeaked (pp : P → ℝ) :
    WeakPrefExtendsSinglePeaked pp (euclideanWeakPref pp) := by
  intro j x y h
  exact h.abs_le

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem euclideanStrictPref_impliesWeak (pp : P → ℝ) :
    StrictPrefImpliesWeak (euclideanStrictPref pp) (euclideanWeakPref pp) := by
  intro j x y h
  exact le_of_lt h

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem euclideanStrictPref_trans (pp : P → ℝ) :
    StrictPrefTrans (euclideanStrictPref pp) := by
  intro j x y z hxy hyz
  exact lt_trans hxy hyz

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem euclideanWeakStrictPrefTrans (pp : P → ℝ) :
    WeakStrictPrefTrans (euclideanStrictPref pp) (euclideanWeakPref pp) := by
  intro j x y z hxy hyz
  unfold euclideanStrictPref euclideanWeakPref Prefers at *
  exact lt_of_le_of_lt hxy hyz

/-! ## A right-tie single-peaked preference

The following "closer, breaking equidistant ties toward the right" preference
is a concrete asymmetric instance of the compatibility axioms used below.  At
peak `0` it strictly prefers `1` to `-1`, whereas Euclidean distance is
indifferent between them. -/

/-- A single-peaked strict preference that breaks equidistant ties toward the
larger (right) outcome.  It is asymmetric: at peak `0` it strictly prefers `1`
to `-1` but not `-1` to `1`. -/
def rightTieStrictPref (pp : P → ℝ) : StrictOutcomePref P :=
  fun j x y => |x - pp j| < |y - pp j| ∨ (|x - pp j| = |y - pp j| ∧ y < x)

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem rightTieStrictPref_irrefl (pp : P → ℝ) :
    StrictPrefIrrefl (rightTieStrictPref pp) := by
  intro j x h
  rcases h with h | ⟨_, h⟩ <;> exact absurd h (lt_irrefl _)

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem rightTieStrictPref_respectsSinglePeaked (pp : P → ℝ) :
    StrictPrefRespectsSinglePeaked pp (rightTieStrictPref pp) := by
  intro j x y h hsp
  have hle : |x - pp j| ≤ |y - pp j| := by
    rcases h with h | ⟨h, _⟩
    · exact le_of_lt h
    · exact le_of_eq h
  exact absurd hsp.abs_lt (not_lt.mpr hle)

omit [Fintype P] [Nonempty P] [LinearOrder P] in
theorem rightTieStrictPref_extendsSinglePeaked (pp : P → ℝ) :
    StrictPrefExtendsSinglePeaked pp (rightTieStrictPref pp) := by
  intro j x y h
  exact Or.inl h.abs_lt

/-- The tie-breaking preference is asymmetric and non-Euclidean: at
peak `0` it strictly prefers `1` to `-1`, while it neither prefers `-1` to `1`
nor is Euclidean distance able to distinguish them. -/
example :
    rightTieStrictPref (fun _ : Fin 1 => (0 : ℝ)) 0 1 (-1)
      ∧ ¬ rightTieStrictPref (fun _ : Fin 1 => (0 : ℝ)) 0 (-1) 1
      ∧ ¬ euclideanStrictPref (fun _ : Fin 1 => (0 : ℝ)) 0 1 (-1) := by
  refine ⟨Or.inr ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · rintro (h | ⟨_, h⟩) <;> norm_num at h
  · simp only [euclideanStrictPref, Prefers]; norm_num

/-- **Theorem 2** for the right-tie preference: the manipulability
characterization specializes from `proxy_manipulation_iff_of_singlePeaked` to
this non-Euclidean, non-symmetric single-peaked preference. -/
theorem proxy_manipulation_iff_rightTie (pp : P → ℝ) (q : F → ℝ) :
    (∃ (j : P) (r : ℝ),
        rightTieStrictPref pp j (outcome (Function.update pp j r) q) (outcome pp q))
      ↔ (∀ j, pp j ≠ socialMedian pp q)
        ∧ (∃ j, pp j < socialMedian pp q)
        ∧ (∃ j, socialMedian pp q < pp j) :=
  proxy_manipulation_iff_of_singlePeaked
    (rightTieStrictPref_irrefl pp)
    (rightTieStrictPref_respectsSinglePeaked pp)
    (rightTieStrictPref_extendsSinglePeaked pp) q

/-! ## Exact better responses -/

/-- Exact-preference better response: the new outcome is strictly preferred to
the old outcome by the chosen strict preference relation. -/
def IsBetterResponseFor (spref : StrictOutcomePref P)
    (_pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) (j : P) (r : ℝ) : Prop :=
  spref j (outcome (Function.update s j r) q) (outcome s q)

/-- Preference-parametric pure Nash equilibrium. -/
def IsPNEFor (spref : StrictOutcomePref P)
    (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) : Prop :=
  ∀ j r, ¬ IsBetterResponseFor spref pp q s j r

theorem IsBetterResponseFor.ne {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref) {j : P} {r : ℝ}
    (h : IsBetterResponseFor spref pp q s j r) :
    outcome (Function.update s j r) q ≠ outcome s q := by
  intro heq
  unfold IsBetterResponseFor at h
  rw [heq] at h
  exact hirr j (outcome s q) h

/-- Exact better responses whose strict preferences respect single-peakedness
are valid better responses in the existing permissive single-peaked layer. -/
theorem IsBetterResponseFor.toIsBetterResponse {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    {j : P} {r : ℝ}
    (h : IsBetterResponseFor spref pp q s j r) :
    IsBetterResponse pp q s j r := by
  exact ⟨h.ne hirr, hcompat j h⟩

theorem isBetterResponseFor_of_spPrefers {spref : StrictOutcomePref P}
    (hext : StrictPrefExtendsSinglePeaked pp spref) {j : P} {r : ℝ}
    (h : SPPrefers (pp j) (outcome (Function.update s j r) q) (outcome s q)) :
    IsBetterResponseFor spref pp q s j r :=
  hext j h

theorem isBetterResponseFor_euclidean_iff {j : P} {r : ℝ} :
    IsBetterResponseFor (euclideanStrictPref pp) pp q s j r
      ↔ Prefers pp j (outcome (Function.update s j r) q) (outcome s q) := by
  rfl

/-- The existing Euclidean bridge, restated through exact preferences. -/
theorem IsBetterResponseFor.toIsBetterResponse_euclidean {j : P} {r : ℝ}
    (h : IsBetterResponseFor (euclideanStrictPref pp) pp q s j r) :
    IsBetterResponse pp q s j r :=
  h.toIsBetterResponse (euclideanStrictPref_irrefl pp)
    (euclideanStrictPref_respectsSinglePeaked pp)

/-! ## Exact monotone dynamics -/

/-- A monotone step whose moving report is an exact better response. -/
def MonotoneStepFor (spref : StrictOutcomePref P)
    (pp : P → ℝ) (q : F → ℝ) (s s' : P → ℝ) : Prop :=
  ∃ j r, IsBetterResponseFor spref pp q s j r ∧ MonotoneReport pp q j r
    ∧ s' = Function.update s j r

/-- Exact-preference monotone dynamics from truth. -/
def IsMonotoneDynamicsFor (spref : StrictOutcomePref P)
    (pp : P → ℝ) (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  σ 0 = pp ∧
    ∀ t, MonotoneStepFor spref pp q (σ t) (σ (t + 1)) ∨ σ (t + 1) = σ t

theorem MonotoneStepFor.toMonotoneStep {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    {s' : P → ℝ} (h : MonotoneStepFor spref pp q s s') :
    MonotoneStep pp q s s' := by
  obtain ⟨j, r, hbr, hmono, hs'⟩ := h
  exact ⟨j, r, hbr.toIsBetterResponse hirr hcompat, hmono, hs'⟩

theorem IsMonotoneDynamicsFor.toIsMonotoneDynamics {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    {σ : ℕ → P → ℝ} (h : IsMonotoneDynamicsFor spref pp q σ) :
    IsMonotoneDynamics pp q σ := by
  refine ⟨h.1, fun t => ?_⟩
  rcases h.2 t with hstep | hrest
  · exact Or.inl (hstep.toMonotoneStep hirr hcompat)
  · exact Or.inr hrest

theorem socialMedian_eq_of_isMonotoneDynamicsFor {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    {σ : ℕ → P → ℝ} (h : IsMonotoneDynamicsFor spref pp q σ) (t : ℕ) :
    socialMedian (σ t) q = socialMedian pp q :=
  socialMedian_eq_of_isMonotoneDynamics
    (h.toIsMonotoneDynamics hirr hcompat) t

theorem monotoneStepFor_dist_le
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    {j : P} {r : ℝ} (hmono : MonotoneReport pp q j r) (hj : j ≠ winner s q) :
    |outcome (Function.update s j r) q - socialMedian pp q|
      ≤ |outcome s q - socialMedian pp q| :=
  monotoneStep_dist_le hside hmed hmono hj

theorem monotoneStepFor_dist_lt {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    (hside : SameSide pp q s) (hmed : socialMedian s q = socialMedian pp q)
    {j : P} {r : ℝ} (hbr : IsBetterResponseFor spref pp q s j r)
    (hmono : MonotoneReport pp q j r) (hj : j ≠ winner s q)
    (htie : ∀ k k', |Function.update s j r k - socialMedian pp q|
        = |Function.update s j r k' - socialMedian pp q|
      → Function.update s j r k = Function.update s j r k') :
    |outcome (Function.update s j r) q - socialMedian pp q|
      < |outcome s q - socialMedian pp q| :=
  monotoneStep_dist_lt hside hmed (hbr.toIsBetterResponse hirr hcompat)
    hmono hj htie

/-- Exact-preference meta-move. -/
def MetaMoveFor (spref : StrictOutcomePref P)
    (pp : P → ℝ) (q : F → ℝ) (j : P) (σ : ℕ → P → ℝ) (ℓ : ℕ) : Prop :=
  0 < ℓ ∧ j ≠ winner (σ 0) q
    ∧ (∀ i < ℓ, ∃ r, IsBetterResponseFor spref pp q (σ i) j r
        ∧ MonotoneReport pp q j r ∧ σ (i + 1) = Function.update (σ i) j r)
    ∧ ∀ i, 0 < i → i ≤ ℓ → winner (σ i) q = j

theorem MetaMoveFor.toMetaMove {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMoveFor spref pp q j σ ℓ) :
    MetaMove pp q j σ ℓ := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro i hi
  obtain ⟨r, hbr, hmono, hs⟩ := h.2.2.1 i hi
  exact ⟨r, hbr.toIsBetterResponse hirr hcompat, hmono, hs⟩

theorem metaMoveFor_dist_le {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMoveFor spref pp q j σ ℓ)
    (hside : SameSide pp q (σ 0))
    (hmed : socialMedian (σ 0) q = socialMedian pp q) {i : ℕ} (hi : i ≤ ℓ) :
    |outcome (σ i) q - socialMedian pp q|
      ≤ |outcome (σ 0) q - socialMedian pp q| :=
  metaMove_dist_le (h.toMetaMove hirr hcompat) hside hmed hi

theorem metaMoveFor_dist_lt {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMoveFor spref pp q j σ ℓ)
    (hside : SameSide pp q (σ 0))
    (hmed : socialMedian (σ 0) q = socialMedian pp q)
    (hsep : ∀ k, |outcome (σ 0) q - socialMedian pp q|
      ≤ |pp k - socialMedian pp q|)
    (htie : ∀ k k', |σ ℓ k - socialMedian pp q| = |σ ℓ k' - socialMedian pp q|
      → σ ℓ k = σ ℓ k') :
    |outcome (σ ℓ) q - socialMedian pp q|
      < |outcome (σ 0) q - socialMedian pp q| :=
  metaMove_dist_lt (h.toMetaMove hirr hcompat) hside hmed hsep htie

/-- Along an exact-preference meta-move, strict transitivity chains the step
improvements: the terminal outcome is strictly preferred to the initial
outcome by the moving proxy. -/
theorem MetaMoveFor.prefers_terminal_outcome {spref : StrictOutcomePref P}
    (htrans : StrictPrefTrans spref)
    {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMoveFor spref pp q j σ ℓ) :
    spref j (outcome (σ ℓ) q) (outcome (σ 0) q) := by
  have hchain : ∀ n, n ≤ ℓ → 0 < n →
      spref j (outcome (σ n) q) (outcome (σ 0) q) := by
    intro n hn hpos
    induction n with
    | zero => exact (Nat.not_lt_zero 0 hpos).elim
    | succ n ih =>
        obtain ⟨r, hbr, -, hupd⟩ := h.2.2.1 n (Nat.lt_of_succ_le hn)
        have hstep : spref j (outcome (σ (n + 1)) q) (outcome (σ n) q) := by
          simpa [IsBetterResponseFor, hupd] using hbr
        cases n with
        | zero =>
            simpa using hstep
        | succ n' =>
            exact htrans j hstep
              (ih (Nat.le_trans (Nat.le_succ _) hn) (Nat.succ_pos _))
  exact hchain ℓ (le_refl ℓ) h.1

/-- Exact-preference strict meta-move progress.  For fixed transitive
preferences, the peak-separation hypothesis needed by the permissive
single-peaked reading is unnecessary: if terminal mirror ties are excluded,
equal terminal and initial median-distance would force the same selected
outcome, contradicting the chained strict improvement. -/
theorem metaMoveFor_dist_lt_of_strictTrans {spref : StrictOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    (htrans : StrictPrefTrans spref)
    {j : P} {σ : ℕ → P → ℝ} {ℓ : ℕ}
    (h : MetaMoveFor spref pp q j σ ℓ)
    (hside : SameSide pp q (σ 0))
    (hmed : socialMedian (σ 0) q = socialMedian pp q)
    (htie : ∀ k k', |σ ℓ k - socialMedian pp q| = |σ ℓ k' - socialMedian pp q|
      → σ ℓ k = σ ℓ k') :
    |outcome (σ ℓ) q - socialMedian pp q|
      < |outcome (σ 0) q - socialMedian pp q| := by
  rcases lt_or_eq_of_le
      (metaMoveFor_dist_le hirr hcompat h hside hmed (le_refl ℓ)) with hlt | heq
  · exact hlt
  exfalso
  have hmeta : MetaMove pp q j σ ℓ := h.toMetaMove hirr hcompat
  have hwinℓ : winner (σ ℓ) q = j := h.2.2.2 ℓ h.1 (le_refl ℓ)
  have houtℓ : outcome (σ ℓ) q = σ ℓ j := by rw [outcome, hwinℓ]
  have hold : σ ℓ (winner (σ 0) q) = σ 0 (winner (σ 0) q) :=
    hmeta.winner_report_eq (le_refl ℓ)
  have hsameReport : σ ℓ j = σ ℓ (winner (σ 0) q) := by
    exact htie j (winner (σ 0) q) (by
      rw [← houtℓ, hold]
      exact heq)
  have hout_eq : outcome (σ ℓ) q = outcome (σ 0) q := by
    rw [houtℓ, hsameReport, hold]
    rfl
  have hpref := h.prefers_terminal_outcome htrans
  rw [hout_eq] at hpref
  exact hirr j (outcome (σ 0) q) hpref

/-! ## Exact truth orientation -/

/-- Truth is weakly best among exact better responses: truthful reporting is
itself an exact better response, and its outcome is weakly preferred to the
outcome of every exact better response. -/
def TruthWeaklyBestAmongBetterResponsesFor
    (spref : StrictOutcomePref P) (wpref : WeakOutcomePref P)
    (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) (j : P) : Prop :=
  IsBetterResponseFor spref pp q s j (pp j)
    ∧ ∀ r, IsBetterResponseFor spref pp q s j r →
      wpref j (outcome (Function.update s j (pp j)) q)
        (outcome (Function.update s j r) q)

/-- Exact-preference truth-oriented choice. -/
def TruthOrientedChoiceFor
    (spref : StrictOutcomePref P) (wpref : WeakOutcomePref P)
    (pp : P → ℝ) (q : F → ℝ) (s : P → ℝ) (j : P) (r : ℝ) : Prop :=
  TruthWeaklyBestAmongBetterResponsesFor spref wpref pp q s j → r = pp j

/-- A truth-oriented exact better-response step. -/
def TruthOrientedStepFor
    (spref : StrictOutcomePref P) (wpref : WeakOutcomePref P)
    (pp : P → ℝ) (q : F → ℝ) (s s' : P → ℝ) : Prop :=
  ∃ j r, IsBetterResponseFor spref pp q s j r
    ∧ TruthOrientedChoiceFor spref wpref pp q s j r
    ∧ s' = Function.update s j r

/-- Truth-oriented exact-preference dynamics from truth. -/
def IsTruthOrientedDynamicsFor
    (spref : StrictOutcomePref P) (wpref : WeakOutcomePref P)
    (pp : P → ℝ) (q : F → ℝ) (σ : ℕ → P → ℝ) : Prop :=
  σ 0 = pp ∧
    ∀ t, TruthOrientedStepFor spref wpref pp q (σ t) (σ (t + 1))
      ∨ σ (t + 1) = σ t

/-- If the forced single-peaked layer says truth is weakly best, then any exact
better response witnessing the current move turns that forced statement into
an exact-preference weak-best statement. -/
theorem truthWeaklyBestAmongBetterResponsesFor_of_forced
    {spref : StrictOutcomePref P} {wpref : WeakOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    (hweak : WeakPrefExtendsSinglePeaked pp wpref)
    (htrans : WeakStrictPrefTrans spref wpref)
    {j : P} {r₀ : ℝ}
    (hforced : TruthWeaklyBestAmongBetterResponses pp q s j)
    (hbr₀ : IsBetterResponseFor spref pp q s j r₀) :
    TruthWeaklyBestAmongBetterResponsesFor spref wpref pp q s j := by
  have hbr₀_old : IsBetterResponse pp q s j r₀ :=
    hbr₀.toIsBetterResponse hirr hcompat
  constructor
  · exact htrans j (hweak j (hforced.2 r₀ hbr₀_old)) hbr₀
  · intro r hbr
    exact hweak j (hforced.2 r (hbr.toIsBetterResponse hirr hcompat))

/-- The exact-preference version of the violating-report forcing lemma used in
the truth-oriented boundedness theorem. -/
theorem truthWeaklyBestAmongBetterResponsesFor_of_violating
    {spref : StrictOutcomePref P} {wpref : WeakOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    (hweak : WeakPrefExtendsSinglePeaked pp wpref)
    (htrans : WeakStrictPrefTrans spref wpref)
    {s : P → ℝ} {j : P} {r : ℝ}
    (hinv : StrongBandInvariant pp q s)
    (hbr : IsBetterResponseFor spref pp q s j r)
    (hviol : BandViolatingReport pp q j r ∨ InitialWinnerDriftReport pp q j r) :
    TruthWeaklyBestAmongBetterResponsesFor spref wpref pp q s j :=
  truthWeaklyBestAmongBetterResponsesFor_of_forced hirr hcompat hweak htrans
    (truthWeaklyBestAmongBetterResponses_of_violating hinv
      (hbr.toIsBetterResponse hirr hcompat) hviol)
    hbr

theorem strongBandInvariant_of_isTruthOrientedDynamicsFor_of_forcing
    {spref : StrictOutcomePref P} {wpref : WeakOutcomePref P} {σ : ℕ → P → ℝ}
    (hdyn : IsTruthOrientedDynamicsFor spref wpref pp q σ)
    (hforce : ∀ t j r, StrongBandInvariant pp q (σ t) →
      IsBetterResponseFor spref pp q (σ t) j r →
        (BandViolatingReport pp q j r ∨ InitialWinnerDriftReport pp q j r) →
          TruthWeaklyBestAmongBetterResponsesFor spref wpref pp q (σ t) j) :
    ∀ t, StrongBandInvariant pp q (σ t) := by
  intro t
  induction t with
  | zero =>
      rw [hdyn.1]
      exact strongBandInvariant_self pp q
  | succ t ih =>
      rcases hdyn.2 t with hstep | hrest
      · obtain ⟨j, r, hbr, htruth, hs'⟩ := hstep
        rw [hs']
        refine ih.update_of_not_violating ?_ ?_
        · intro hv
          have hbest := hforce t j r ih hbr (Or.inl hv)
          rw [htruth hbest] at hv
          exact not_bandViolatingReport_truthful (pp := pp) (q := q) j hv
        · intro hv
          have hbest := hforce t j r ih hbr (Or.inr hv)
          rw [htruth hbest] at hv
          exact not_initialWinnerDriftReport_truthful (pp := pp) (q := q) j hv
      · rw [hrest]
        exact ih

/-- **Preference-parametric Theorem 3.**  Truth-oriented exact-preference
better-response dynamics preserve the band and initial-winner anchor
invariants, provided strict and weak preferences are compatible with
single-peakedness. -/
theorem strongBandInvariant_of_isTruthOrientedDynamicsFor
    {spref : StrictOutcomePref P} {wpref : WeakOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    (hweak : WeakPrefExtendsSinglePeaked pp wpref)
    (htrans : WeakStrictPrefTrans spref wpref)
    {σ : ℕ → P → ℝ}
    (hdyn : IsTruthOrientedDynamicsFor spref wpref pp q σ) (t : ℕ) :
    StrongBandInvariant pp q (σ t) :=
  strongBandInvariant_of_isTruthOrientedDynamicsFor_of_forcing hdyn
    (fun _ _ _ hinv hbr hviol =>
      truthWeaklyBestAmongBetterResponsesFor_of_violating
        hirr hcompat hweak htrans hinv hbr hviol) t

/-- Preference-parametric Corollary 1: along exact truth-oriented dynamics,
the current median and current outcome stay in the initial `Delta` band. -/
theorem median_and_outcome_mem_band_of_isTruthOrientedDynamicsFor
    {spref : StrictOutcomePref P} {wpref : WeakOutcomePref P}
    (hirr : StrictPrefIrrefl spref)
    (hcompat : StrictPrefRespectsSinglePeaked pp spref)
    (hweak : WeakPrefExtendsSinglePeaked pp wpref)
    (htrans : WeakStrictPrefTrans spref wpref)
    {σ : ℕ → P → ℝ}
    (hdyn : IsTruthOrientedDynamicsFor spref wpref pp q σ) (t : ℕ) :
    (socialMedian pp q - initialDelta pp q ≤ socialMedian (σ t) q ∧
        socialMedian (σ t) q ≤ socialMedian pp q + initialDelta pp q) ∧
      (socialMedian pp q - initialDelta pp q ≤ outcome (σ t) q ∧
        outcome (σ t) q ≤ socialMedian pp q + initialDelta pp q) := by
  have hinv :=
    strongBandInvariant_of_isTruthOrientedDynamicsFor
      hirr hcompat hweak htrans hdyn t
  exact ⟨socialMedian_mem_initialDelta_band_of_weakPeakBand hinv.1,
    outcome_mem_band_of_strongBandInvariant hinv⟩

/-! ## Exact dominating manipulations -/

/-- Exact-preference domination over an information set: weakly better at every
consistent profile, strictly better at some consistent profile. -/
def DominatesOverFor (spref : StrictOutcomePref P) (wpref : WeakOutcomePref P)
    (_pp : P → ℝ) (s : P → ℝ) (Q : Set (F → ℝ)) (j : P) (r : ℝ) : Prop :=
  (∀ q ∈ Q,
      wpref j (outcome (Function.update s j r) q) (outcome s q))
    ∧ ∃ q ∈ Q,
      spref j (outcome (Function.update s j r) q) (outcome s q)

/-- Exact-preference dominating manipulation for a winner-poll information
set. -/
def IsDominatingManipulationFor (spref : StrictOutcomePref P) (wpref : WeakOutcomePref P)
    (F : Type*) [Fintype F]
    (pp : P → ℝ) (s : P → ℝ) (jw j : P) (r : ℝ) : Prop :=
  DominatesOverFor spref wpref pp s (winnerInfoSet (F := F) s jw) j r

theorem DominatesOverFor.true_profile_weak {spref : StrictOutcomePref P}
    {wpref : WeakOutcomePref P} {q : F → ℝ} {j : P} {r : ℝ}
    (h : IsDominatingManipulationFor spref wpref F pp s (winner s q) j r) :
    wpref j (outcome (Function.update s j r) q) (outcome s q) :=
  h.1 q (mem_winnerInfoSet_self s q)

theorem dominatesOverFor_singleton_iff {spref : StrictOutcomePref P}
    {wpref : WeakOutcomePref P} (hsw : StrictPrefImpliesWeak spref wpref)
    {q₀ : F → ℝ} {j : P} {r : ℝ} :
    DominatesOverFor spref wpref pp s {q₀} j r
      ↔ spref j (outcome (Function.update s j r) q₀) (outcome s q₀) := by
  constructor
  · rintro ⟨-, q, hq, hpref⟩
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hpref
  · intro h
    refine ⟨fun q hq => ?_, q₀, Set.mem_singleton q₀, h⟩
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hsw j h

theorem isBetterResponseFor_of_dominatesOverFor_singleton {spref : StrictOutcomePref P}
    {wpref : WeakOutcomePref P} (hsw : StrictPrefImpliesWeak spref wpref)
    {q₀ : F → ℝ} {j : P} {r : ℝ}
    (h : DominatesOverFor spref wpref pp s {q₀} j r) :
    IsBetterResponseFor spref pp q₀ s j r :=
  (dominatesOverFor_singleton_iff (s := s) hsw).mp h

/-- Exact domination that is forced by single-peakedness implies the existing
Euclidean domination predicate whenever weak and strict preferences are the
Euclidean ones. -/
theorem dominatesOverFor_euclidean_iff {Q : Set (F → ℝ)} {j : P} {r : ℝ} :
    DominatesOverFor (euclideanStrictPref pp) (euclideanWeakPref pp) pp s Q j r
      ↔ DominatesOver pp s Q j r := by
  rfl

end ProxyVoting

end GameTheory
