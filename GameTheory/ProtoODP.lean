import GameTheory.ProtoSPE
import Math.ProbabilityMassFunction
import Math.Probability

/-!
# One-Shot Deviation Principle on Protocol

The one-shot deviation principle (ODP) characterizes subgame-perfect equilibria:
a profile is SPE if and only if no player can profitably deviate at any single round.

## Main definitions

- `Protocol.oneShotDevEval` — evaluate with a deviation at exactly one round
- `Protocol.HasNoOneShotDeviation` — no profitable single-round deviation
- `Round.ActionIrrelevant` — player's action doesn't affect transition
- `Protocol.IsPerfectInfo` — views determine state
- `Protocol.IsPerfectInfoRelevant` — PI or action-irrelevant at each round
- `Protocol.odp` — the equivalence (SPE ↔ no OSD under PI-relevant)

## Design

The hard direction (no OSD → SPE) is proved by induction on remaining rounds,
following the approach of `SequentialODP.hasNoOneShotDeviation_spe`. The easy
direction requires PI-relevant conditions.
-/

namespace GameTheory

open Math.Probability

variable {n : ℕ} {S V A Sig : Type}

-- ============================================================================
-- One-shot deviations
-- ============================================================================

open Classical in
/-- A one-shot deviation at round `k`: player `i` uses `si'` at round `k` only,
    and follows `σ` at all other rounds. Returns the final state distribution. -/
noncomputable def Protocol.oneShotDevEval (G : Protocol n S V A Sig)
    (k : ℕ) (s : S) (σ : PureProfile n V A) (i : Fin n) (si' : PureStrategy V A) :
    PMF S :=
  match G.rounds.drop k with
  | [] => PMF.pure s
  | r :: rest =>
    (r.eval (Function.update σ i si') s).bind (evalRounds rest σ)

/-- Expected utility under a one-shot deviation. -/
noncomputable def Protocol.oneShotDevEu (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) (k : ℕ) (s : S) (σ : PureProfile n V A)
    (i : Fin n) (si' : PureStrategy V A) : ℝ :=
  expect (G.oneShotDevEval k s σ i si') (fun s' => u s' i)

open Classical in
/-- No player has a profitable one-shot deviation at any subgame. -/
def Protocol.HasNoOneShotDeviation (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) (σ : PureProfile n V A) : Prop :=
  ∀ (k : ℕ) (s : S) (i : Fin n) (si' : PureStrategy V A),
    G.subgameEu u k s σ i ≥ G.oneShotDevEu u k s σ i si'

-- ============================================================================
-- Perfect information / relevance conditions
-- ============================================================================

open Classical in
/-- Player `i`'s action at state `s` does not affect the transition in round `r`. -/
def Round.ActionIrrelevant (r : Round n S V A Sig) (i : Fin n) (s : S) : Prop :=
  ∀ (_sig : Fin n → Sig) (acts : Fin n → Option A) (a' : Option A),
    r.transition s (Function.update acts i a') = r.transition s acts

/-- A protocol has perfect information: each player's view determines the state. -/
def Protocol.IsPerfectInfo (G : Protocol n S V A Sig) : Prop :=
  ∀ (r : Round n S V A Sig), r ∈ G.rounds →
    ∀ (i : Fin n) (s₁ s₂ : S) (sig₁ sig₂ : Fin n → Sig),
      r.view i s₁ (sig₁ i) = r.view i s₂ (sig₂ i) → s₁ = s₂

/-- Perfect-information-relevant: for each player and round, either
    (1) the player's view determines the state, or
    (2) the player's action is irrelevant at that state.
    This is the condition needed for the ODP easy direction. -/
def Protocol.IsPerfectInfoRelevant (G : Protocol n S V A Sig) : Prop :=
  ∀ (r : Round n S V A Sig), r ∈ G.rounds →
    ∀ (i : Fin n) (s : S),
      (∀ (s₂ : S) (sig₁ sig₂ : Fin n → Sig),
        r.view i s (sig₁ i) = r.view i s₂ (sig₂ i) → s = s₂)
      ∨ r.ActionIrrelevant i s

/-- Perfect information implies perfect-information-relevant. -/
theorem Protocol.perfectInfo_isPerfectInfoRelevant (G : Protocol n S V A Sig)
    (hPI : G.IsPerfectInfo) : G.IsPerfectInfoRelevant := by
  intro r hr i s
  exact Or.inl (fun s₂ sig₁ sig₂ h => hPI r hr i s s₂ sig₁ sig₂ h)

-- ============================================================================
-- Hard direction: no OSD → SPE
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- Key inductive lemma for the hard direction: for any suffix of rounds,
    no-OSD implies Nash in the subgame defined by that suffix. -/
private theorem noOSD_implies_nash_suffix [Fintype S]
    (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) (σ : PureProfile n V A)
    (hnosd : G.HasNoOneShotDeviation u σ)
    (rounds : List (Round n S V A Sig))
    (k : ℕ) (hk : rounds = G.rounds.drop k)
    (s : S) (i : Fin n) (si' : PureStrategy V A) :
    expect (evalRounds rounds σ s) (fun s' => u s' i) ≥
      expect (evalRounds rounds (Function.update σ i si') s) (fun s' => u s' i) := by
  induction rounds generalizing k s with
  | nil => simp only [evalRounds_nil, expect_pure]; exact le_refl _
  | cons r rest ih =>
    -- rest = G.rounds.drop (k + 1)
    have hrest : rest = G.rounds.drop (k + 1) := by
      have h1 : G.rounds.drop (k + 1) = (G.rounds.drop k).tail :=
        List.drop_add_one_eq_tail_drop
      rw [h1, ← hk]; rfl
    -- Decompose both sides via evalRounds_cons + expect_bind
    rw [evalRounds_cons, evalRounds_cons, expect_bind, expect_bind]
    -- Continuation monotonicity from IH
    have h_ih : ∀ s', expect (evalRounds rest σ s') (fun s' => u s' i) ≥
        expect (evalRounds rest (Function.update σ i si') s') (fun s' => u s' i) :=
      fun s' => ih (k + 1) hrest s'
    -- No-OSD at round k: unpack and unfold
    have hnosd_k := hnosd k s i si'
    simp only [Protocol.subgameEu, Protocol.subgameEval, ← hk,
      evalRounds_cons, expect_bind] at hnosd_k
    -- hnosd_k: E[r.eval σ s][V_σ] ≥ oneShotDevEu
    -- Unfold oneShotDevEu to get the same V_σ on the RHS
    simp only [Protocol.oneShotDevEu, Protocol.oneShotDevEval, ← hk,
      expect_bind] at hnosd_k
    -- hnosd_k: E[r.eval σ s][V_σ] ≥ E[r.eval (update σ i si') s][V_σ]
    -- Monotonicity: E[r.eval (update σ i si') s][V_dev] ≤ E[r.eval (update σ i si') s][V_σ]
    have h_mono : expect (r.eval (Function.update σ i si') s)
          (fun s' => expect (evalRounds rest (Function.update σ i si') s')
            (fun s' => u s' i)) ≤
        expect (r.eval (Function.update σ i si') s)
          (fun s' => expect (evalRounds rest σ s') (fun s' => u s' i)) :=
      Math.ProbabilityMassFunction.expect_mono_of_pointwise _ _ _ (fun s' => h_ih s')
    linarith

set_option linter.unusedFintypeInType false in
open Classical in
/-- **ODP Hard Direction**: no profitable one-shot deviation implies SPE. -/
theorem Protocol.hasNoOneShotDeviation_spe (G : Protocol n S V A Sig)
    [Fintype S]
    (u : S → Fin n → ℝ) (σ : PureProfile n V A)
    (hnosd : G.HasNoOneShotDeviation u σ) :
    G.IsSubgamePerfect u σ := by
  intro k s i si'
  exact noOSD_implies_nash_suffix G u σ hnosd (G.rounds.drop k) k rfl s i si'

-- ============================================================================
-- View separation and evalRounds congruence
-- ============================================================================

/-- Views at different rounds are distinguishable: for any two distinct rounds
    in the protocol, their view ranges (for each player) are disjoint.
    This ensures backward induction strategies can be encoded as memoryless
    pure strategies without cross-round conflicts. -/
def Protocol.ViewSeparated (G : Protocol n S V A Sig) : Prop :=
  ∀ ⦃k₁ k₂ : ℕ⦄ (hk₁ : k₁ < G.rounds.length) (hk₂ : k₂ < G.rounds.length),
    k₁ ≠ k₂ →
    ∀ (i : Fin n) (s₁ s₂ : S) (sig₁ sig₂ : Fin n → Sig),
      (G.rounds[k₁]).view i s₁ (sig₁ i) ≠ (G.rounds[k₂]).view i s₂ (sig₂ i)

/-- View disjointness between a round and a list: the round's views don't
    overlap with any round in the list. -/
def viewDisjointFromList (r : Round n S V A Sig)
    (rest : List (Round n S V A Sig)) : Prop :=
  ∀ r' ∈ rest, ∀ (i : Fin n) (s₁ s₂ : S) (sig₁ sig₂ : Fin n → Sig),
    r.view i s₁ (sig₁ i) ≠ r'.view i s₂ (sig₂ i)

/-- `evalRounds` depends on `σ` only through the views produced at the rounds
    in the list. If two profiles agree on all such views, the evaluations
    match. -/
theorem evalRounds_congr (rounds : List (Round n S V A Sig))
    (σ₁ σ₂ : PureProfile n V A)
    (h : ∀ r ∈ rounds, ∀ (j : Fin n) (s : S) (sig : Fin n → Sig),
      σ₁ j (r.view j s (sig j)) = σ₂ j (r.view j s (sig j)))
    (s : S) :
    evalRounds rounds σ₁ s = evalRounds rounds σ₂ s := by
  induction rounds generalizing s with
  | nil => rfl
  | cons r rest ih =>
    rw [evalRounds_cons, evalRounds_cons]
    have heval : r.eval σ₁ s = r.eval σ₂ s := by
      simp only [Round.eval]
      congr 1; funext sig; congr 1; funext j
      exact h r (.head rest) j s sig
    rw [heval]
    congr 1; funext s'
    exact ih (fun r' hr' => h r' (.tail r hr')) s'

-- ============================================================================
-- Easy direction: SPE → no OSD (with ViewSeparated)
-- ============================================================================

open Classical in
/-- **ODP Easy Direction**: SPE implies no profitable one-shot deviation
    under `ViewSeparated` (views at different rounds are disjoint per player).

    The key step constructs a single `si'' : PureStrategy V A` that acts like
    `si'` on round-`k` views and like `σ i` elsewhere. `ViewSeparated` ensures
    no conflict, so the one-shot deviation at round `k` equals the full deviation
    with `si''`. SPE applied to `si''` then gives the result. -/
theorem Protocol.spe_hasNoOneShotDeviation (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) (σ : PureProfile n V A)
    (hVS : G.ViewSeparated)
    (hspe : G.IsSubgamePerfect u σ) :
    G.HasNoOneShotDeviation u σ := by
  intro k s i si'
  -- Unfold OSD goal to: subgameEu ≥ oneShotDevEu
  -- Both sides use G.rounds.drop k
  match hd : G.rounds.drop k with
  | [] =>
    simp only [Protocol.subgameEu, Protocol.subgameEval,
      Protocol.oneShotDevEu, Protocol.oneShotDevEval, hd,
      evalRounds_nil, expect_pure]; exact le_refl _
  | r :: rest =>
    -- Derive ViewSeparated for r vs rest
    have hk_lt : k < G.rounds.length := by
      by_contra h; push_neg at h
      simp [List.drop_eq_nil_of_le h] at hd
    have hVD : viewDisjointFromList r rest := by
      intro r' hr' j s₁ s₂ sig₁ sig₂
      have ⟨k', hk'mem⟩ := List.get_of_mem hr'
      have hrest_eq : rest = G.rounds.drop (k + 1) := by
        rw [List.drop_add_one_eq_tail_drop, hd]; rfl
      have hk'bound : k + 1 + k'.val < G.rounds.length := by
        have := k'.isLt
        simp [hrest_eq, List.length_drop] at this; omega
      have hrw : r' = G.rounds[k + 1 + k'.val] := by
        conv_lhs => rw [← hk'mem]
        simp [List.get_eq_getElem, hrest_eq, List.getElem_drop]
      have hr_eq : r = G.rounds[k] := by
        have h0 : (G.rounds.drop k)[0]'(by rw [hd]; simp) = r := by
          simp [hd]
        simp only [List.getElem_drop, Nat.add_zero] at h0
        exact h0.symm
      rw [hr_eq, hrw]
      exact hVS hk_lt hk'bound (by omega) j s₁ s₂ sig₁ sig₂
    -- Build si'': si' on round-k views, σ i elsewhere
    let isRkView (v : V) : Prop :=
      ∃ (s' : S) (sig : Fin n → Sig), v = r.view i s' (sig i)
    let si'' : PureStrategy V A :=
      fun v => if isRkView v then si' v else σ i v
    -- Head round: si'' acts like si'
    have hhead : r.eval (Function.update σ i si'') s =
        r.eval (Function.update σ i si') s := by
      simp only [Round.eval]; congr 1; funext sig; congr 1; funext j
      by_cases hij : j = i
      · subst hij; simp only [Function.update_self]
        exact if_pos ⟨s, sig, rfl⟩
      · simp [Function.update_of_ne hij]
    -- Rest rounds: si'' acts like σ i
    have hrest : ∀ s', evalRounds rest (Function.update σ i si'') s' =
        evalRounds rest σ s' := by
      intro s'
      apply evalRounds_congr
      intro r' hr' j s'' sig
      by_cases hij : j = i
      · rw [hij, Function.update_self]
        have hne : ¬isRkView (r'.view i s'' (sig i)) := by
          intro ⟨s₂, sig₂, heq⟩
          exact absurd heq.symm (hVD r' hr' i s₂ s'' sig₂ sig)
        simp only [si'', if_neg hne]
      · simp [Function.update_of_ne hij]
    -- subgameEval with (update σ i si'') = oneShotDevEval
    have hdev_eval : G.subgameEval k s (Function.update σ i si'') =
        G.oneShotDevEval k s σ i si' := by
      simp only [Protocol.subgameEval, Protocol.oneShotDevEval, hd,
        evalRounds_cons]
      rw [hhead]; congr 1; funext s'; exact hrest s'
    -- Apply SPE with si''
    have hspe_k := hspe k s i si''
    simp only [Protocol.subgameEu, hdev_eval] at hspe_k
    exact hspe_k

-- ============================================================================
-- ODP equivalence
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- The one-shot deviation principle: under `ViewSeparated` (and `Fintype S`),
    a profile is SPE iff it has no profitable one-shot deviation. -/
theorem Protocol.odp (G : Protocol n S V A Sig)
    [Fintype S]
    (u : S → Fin n → ℝ) (σ : PureProfile n V A)
    (hVS : G.ViewSeparated) :
    G.IsSubgamePerfect u σ ↔ G.HasNoOneShotDeviation u σ :=
  ⟨G.spe_hasNoOneShotDeviation u σ hVS, G.hasNoOneShotDeviation_spe u σ⟩

end GameTheory
