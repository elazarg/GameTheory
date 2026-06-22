/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Theorems.Kuhn.ObsModel
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import GameTheory.Theorems.Kuhn.CorrelatedRealization.ObsLevel

set_option autoImplicit false

namespace ObsModel

open Math.ProbabilityMassFunction Math.ParameterizedChain Math.TraceRun

attribute [local instance] Fintype.ofFinite

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModel ι σ Obs Act}


/-- Under `PerStepActionRecall`, at most one action can produce a nonzero
transition probability between any pair of states. -/
theorem action_unique_of_psar
    (hPSAR : PerStepActionRecall O) {s t : σ} {a a' : O.JointActionAt s}
    (ha : (O.step s a) t ≠ 0) (ha' : (O.step s a') t ≠ 0) :
    a = a' :=
  funext fun i => hPSAR s s t t a a' ha ha' (fun _ => rfl) (fun _ => rfl) i

/-- Under `PerStepPlayerRecall`, player `i`'s action component is determined by
their own observation at source and target. -/
theorem action_component_unique_of_pspr
    (hPSPR : PerStepPlayerRecall O) (i : ι)
    {s s' t t' : σ} {a : O.JointActionAt s} {a' : O.JointActionAt s'}
    (ha : (O.step s a) t ≠ 0) (ha' : (O.step s' a') t' ≠ 0)
    (hobs : O.obsEq i s s') (hobst : O.obsEq i t t') :
    hobs ▸ a i = a' i :=
  hPSPR.action_eq i ha ha' hobs hobst

/-! ## Bridge: pureRun reachability

The `pureRun` chain produces traces where every state is step-reachable.
This bridges the `Math.ParameterizedChain` execution model with the
`ReachActionTrace` witnesses from `SemanticForm`. -/

section PureRunBridge

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- If `pureRun` reaches a trace with nonzero probability, there exists a
corresponding `ReachActionTrace`. -/
theorem pureRun_nonzero_to_reachActionTrace
    (n : Nat)
    (π : PureProfile O) (ss : List σ)
    (h : pureRun (O.pureStep) O.init n π ss ≠ 0) :
    Nonempty (O.ReachActionTrace ss) := by
  induction n generalizing ss with
  | zero =>
    have hss : ss = [O.init] := by
      by_contra hne; exact h (by simp [pureRun, PMF.pure_apply, hne])
    subst hss; exact ⟨.init⟩
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h
    · simp only [List.concat_eq_append] at h ⊢
      have hp := left_ne_zero_of_mul (pureRun_succ_append .. ▸ h)
      have ht := right_ne_zero_of_mul (pureRun_succ_append .. ▸ h)
      obtain ⟨rat_p⟩ := ih p hp
      rw [pureStep_eq] at ht
      have hlen_p := pureRun_length _ _ m π p hp
      have hp_ne : p ≠ [] := by intro h'; simp [h'] at hlen_p
      have hlast : p.getLast? = some (O.lastState p) := by
        cases hg : p.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hp_ne
        | some s => simp [ObsModel.lastState, ObsModelCore.lastState, hg]
      let a : O.JointActionAt (O.lastState p) :=
        fun i => O.currentObs_projectStates i p ▸ π i (O.projectStates i p)
      exact ⟨.snoc a rat_p hlast ht⟩

/-- If `pureRun` reaches `ss` with nonzero probability, the last state of `ss`
is step-reachable from `O.init`. -/
theorem pureRun_nonzero_last_stepReachable
    (n : Nat)
    (π : PureProfile O) (ss : List σ)
    (h : pureRun (O.pureStep) O.init n π ss ≠ 0) :
    O.StepReachable (O.lastState ss) := by
  obtain ⟨rat⟩ := pureRun_nonzero_to_reachActionTrace n π ss h
  have hlen := pureRun_length _ _ n π ss h
  have hne : ss ≠ [] := by intro h'; simp [h'] at hlen
  have hlast : ss.getLast? = some (O.lastState ss) := by
    cases hg : ss.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hne
    | some s => simp [ObsModel.lastState, ObsModelCore.lastState, hg]
  exact ⟨ss, ⟨rat⟩, hlast⟩

end PureRunBridge

/-! ## Reach factoring under PSAR

Under `PerStepActionRecall`, the reach probability `pureRun(O.pureStep, s₀, n, π, ss)`
depends on `π` only through whether `π` produces the uniquely forced action at each
step. This gives:

1. **Constancy**: nonzero reach probabilities are equal across all profiles
2. **Per-player factoring**: the nonzero condition factors as `∀ i, π_i consistent`
3. **Product preservation**: reweighting a product measure by reach gives a product -/

section ReachFactor

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Under PSAR, nonzero reach probabilities at the same trace are equal.
If two profiles both reach `ss` with nonzero probability, they must produce
the same action at every step, hence have the same reach probability. -/
theorem pureRun_const_of_psar
    (hPSAR : PerStepActionRecall O) (n : Nat) {π π' : PureProfile O} {ss : List σ}
    (h : pureRun (O.pureStep) O.init n π ss ≠ 0)
    (h' : pureRun (O.pureStep) O.init n π' ss ≠ 0) :
    pureRun (O.pureStep) O.init n π ss =
      pureRun (O.pureStep) O.init n π' ss := by
  induction n generalizing ss with
  | zero => simp [pureRun] at h h' ⊢
  | succ k ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h
    · simp only [List.concat_eq_append, pureRun_succ_append] at h h' ⊢
      have hp := left_ne_zero_of_mul h
      have hp' := left_ne_zero_of_mul h'
      have ht := right_ne_zero_of_mul h
      have ht' := right_ne_zero_of_mul h'
      rw [ih hp hp',
          pureStep_eq_of_nonzero_same hPSAR ht ht']

/-- Under PSAR, at a reachable transition, `pureStep` is nonzero iff
the profile produces the same action as any fixed witness profile. -/
theorem pureStep_nonzero_iff_action_eq
    (hPSAR : PerStepActionRecall O) {π₀ : PureProfile O} {ss : List σ} {t : σ}
    (h₀ : O.pureStep π₀ ss t ≠ 0) (π : PureProfile O) :
    O.pureStep π ss t ≠ 0 ↔
      (fun i => π i (O.projectStates i ss)) =
        (fun i => π₀ i (O.projectStates i ss)) := by
  constructor
  · intro hne
    rw [pureStep_eq] at hne h₀
    -- PSAR gives ∀ i, rfl ▸ (▸ π i ...) = ▸ π₀ i ...
    have h := hPSAR _ _ _ _ _ _ hne h₀ (fun _ => rfl) (fun _ => rfl)
    exact funext fun i => by
      have hi : (O.currentObs_projectStates i ss ▸ π i (O.projectStates i ss)) =
          O.currentObs_projectStates i ss ▸ π₀ i (O.projectStates i ss) := h i
      -- Use HEq chain: π i ... ≅ ▸ π i ... = ▸ π₀ i ... ≅ π₀ i ...
      exact eq_of_heq (((rec_heq_of_heq _ HEq.rfl).symm).trans
        ((heq_of_eq hi).trans (rec_heq_of_heq _ HEq.rfl)))
  · intro heq
    have : O.pureStep π ss = O.pureStep π₀ ss := by
      simp only [pureStep_eq]; congr 1; funext i
      exact congrArg (O.currentObs_projectStates i ss ▸ ·) (congr_fun heq i)
    rwa [this]

/-- Under PSAR, `pureRun` is nonzero iff the profile produces the same
action as the witness at every step (prefix). The condition is:
at each prefix `p ++ [t]` of `ss`, the profile agrees on the action at `p`. -/
theorem pureRun_nonzero_iff_action_eq
    (hPSAR : PerStepActionRecall O) (n : Nat) {π₀ : PureProfile O} {ss : List σ}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0) (π : PureProfile O) :
    pureRun (O.pureStep) O.init n π ss ≠ 0 ↔
      (pureRun (O.pureStep) O.init n π ss =
        pureRun (O.pureStep) O.init n π₀ ss) := by
  constructor
  · exact fun h => pureRun_const_of_psar hPSAR n h h₀
  · intro heq; rw [heq]; exact h₀

/-- Under PSAR, `O.pureStep π ss t` factors per-player: it is nonzero iff
each player `i` individually produces the forced action component. -/
theorem pureStep_nonzero_iff_forall_player
    (hPSAR : PerStepActionRecall O) {π₀ : PureProfile O} {ss : List σ} {t : σ}
    (h₀ : O.pureStep π₀ ss t ≠ 0) (π : PureProfile O) :
    O.pureStep π ss t ≠ 0 ↔
      ∀ i, π i (O.projectStates i ss) = π₀ i (O.projectStates i ss) := by
  rw [pureStep_nonzero_iff_action_eq hPSAR h₀]
  exact ⟨fun h i => congr_fun h i, funext⟩

/-- Under PSAR, `pureRun` factors into a trace-dependent constant times a
per-player consistency indicator. If `π` is consistent (nonzero reach),
the reach value equals the witness; otherwise it's zero. -/
theorem pureRun_eq_const_mul_indicator
    (hPSAR : PerStepActionRecall O) (n : Nat) (π₀ : PureProfile O) (ss : List σ)
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (π : PureProfile O) :
    pureRun (O.pureStep) O.init n π ss =
      if pureRun (O.pureStep) O.init n π ss ≠ 0
      then pureRun (O.pureStep) O.init n π₀ ss
      else 0 := by
  split
  · exact pureRun_const_of_psar hPSAR n ‹_› h₀
  · push Not at *; exact le_antisymm (le_of_eq ‹_›) zero_le

/-- Under PSAR, `pureRun` nonzero is equivalent to matching the witness action
at every prefix. Stated inductively: nonzero at `p ++ [t]` iff nonzero at `p`
and action matches at `p`. -/
theorem pureRun_succ_nonzero_iff
    (hPSAR : PerStepActionRecall O) (m : Nat) {π₀ : PureProfile O} {p : List σ} {t : σ}
    (h₀ : pureRun (O.pureStep) O.init (m + 1) π₀ (p ++ [t]) ≠ 0)
    (π : PureProfile O) :
    pureRun (O.pureStep) O.init (m + 1) π (p ++ [t]) ≠ 0 ↔
      pureRun (O.pureStep) O.init m π p ≠ 0 ∧
        ∀ i, π i (O.projectStates i p) = π₀ i (O.projectStates i p) := by
  simp only [pureRun_succ_append] at h₀ ⊢
  have hp₀ := left_ne_zero_of_mul h₀
  have ht₀ := right_ne_zero_of_mul h₀
  constructor
  · intro hne
    exact ⟨left_ne_zero_of_mul hne,
      (pureStep_nonzero_iff_forall_player hPSAR ht₀ π).mp
        (right_ne_zero_of_mul hne)⟩
  · intro ⟨hp, hall⟩
    exact mul_ne_zero hp
      ((pureStep_nonzero_iff_forall_player hPSAR ht₀ π).mpr hall)

/-- Under PSAR, `pureStep` is invariant under changing players who produce
the same action. If `π` and `π'` agree on the action at `ss` (all players
give the same action component), then `O.pureStep π ss = O.pureStep π' ss`. -/
theorem pureStep_eq_of_action_eq {π π' : PureProfile O} {ss : List σ}
    (h : ∀ i, π i (O.projectStates i ss) = π' i (O.projectStates i ss)) :
    O.pureStep π ss = O.pureStep π' ss := by
  simp only [pureStep_eq]; congr 1; funext i
  exact congrArg (O.currentObs_projectStates i ss ▸ ·) (h i)

open Classical in
/-- Under PSAR, reach factors per-player via `Function.update`:
`pureRun π ss ≠ 0` iff for each player `i`, swapping just player `i`'s
component from `π` into the witness `π₀` still gives nonzero reach.

This is the cleanest per-player factoring: each player's consistency
can be tested independently. -/
theorem pureRun_nonzero_iff_update
    (hPSAR : PerStepActionRecall O) (n : Nat) {π₀ : PureProfile O} {ss : List σ}
    (h₀ : pureRun (O.pureStep) O.init n π₀ ss ≠ 0)
    (π : PureProfile O) :
    pureRun (O.pureStep) O.init n π ss ≠ 0 ↔
      ∀ i, pureRun (O.pureStep) O.init n
        (Function.update π₀ i (π i)) ss ≠ 0 := by
  induction n generalizing ss with
  | zero =>
    simp only [pureRun, ne_eq] at h₀ ⊢
    exact ⟨fun _ _ => h₀, fun _ => h₀⟩
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h₀
    · simp only [List.concat_eq_append] at h₀ ⊢
      have hp₀ : pureRun (O.pureStep) O.init m π₀ p ≠ 0 := by
        rw [pureRun_succ_append] at h₀; exact left_ne_zero_of_mul h₀
      rw [pureRun_succ_nonzero_iff hPSAR m h₀]
      constructor
      · -- Forward: π consistent → each update consistent
        intro ⟨hp, hact⟩ i
        exact (pureRun_succ_nonzero_iff hPSAR m h₀
          (Function.update π₀ i (π i))).mpr
          ⟨(ih hp₀).mp hp i, fun j => by
            by_cases hij : j = i
            · subst hij; simp [Function.update_self, hact]
            · simp [Function.update_of_ne hij]⟩
      · -- Backward: each update consistent → π consistent
        intro hall
        constructor
        · exact (ih hp₀).mpr fun i =>
            ((pureRun_succ_nonzero_iff hPSAR m h₀ _).mp (hall i)).1
        · intro i
          have := ((pureRun_succ_nonzero_iff hPSAR m h₀ _).mp (hall i)).2 i
          simp only [Function.update_self] at this
          exact this

end ReachFactor

section Decentralization

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Generalized step-independence-to-trace theorem: if a behavioral profile
`b` satisfies the step-independence property with respect to any
`ν : PMF (PureProfile O)` (not necessarily a product), then
`runDist k b = ν.bind (runDistPure k)`.

This generalizes the step-independence theorem from
`KuhnCore.lean` by replacing `mixedJoint μ` with an arbitrary `ν`. -/
theorem runDist_eq_of_stepIndependence
    (ν : PMF (PureProfile O))
    (b : BehavioralProfile O)
    (hStep : ∀ n,
      ν.bind (fun π =>
        (O.runDistPure n π).bind (fun ss =>
          pushforward (O.stepDist b ss) (fun t => ss ++ [t]))) =
      ν.bind (fun π =>
        (O.runDistPure n π).bind (fun ss =>
          pushforward (O.stepDist (O.pureToBehavioral π) ss)
            (fun t => ss ++ [t])))) (k : Nat) :
    O.runDist k b = ν.bind (fun π => O.runDistPure k π) := by
  change O.toCore.runDist k b =
    ν.bind (fun π => O.toCore.runDistPure k π)
  exact ObsModelCore.runDist_eq_of_correlatedStepIndependence (O := O.toCore) ν b hStep k

/-- Under `PerStepPlayerRecall`, the pure-step action component for player `i`
depends only on player `i`'s observation at obs-equivalent traces. -/
theorem pureStep_component_eq_of_pspr
    (hPSPR : PerStepPlayerRecall O) (i : ι) {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hobs_i : O.projectStates i ss = O.projectStates i ss')
    (hobst_i : O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0) :
    π i (O.projectStates i ss) = hobs_i ▸ π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  have hpspr := hPSPR.action_eq i h1 h2
    (O.obsEq_of_projectStates_getLast i hobs_i) hobst_i
  -- hpspr : obsEq ▸ (currentObs₁ ▸ π i ...) = currentObs₂ ▸ π' i ...
  apply eq_of_heq
  -- Chain: π i ... ≅ ▸π i... ≅ obsEq▸▸π i... = ▸π' i... ≅ π' i... ≅ hobs_i▸π' i...
  have h1' : HEq (π i (O.projectStates i ss)) (π' i (O.projectStates i ss')) :=
    ((rec_heq_of_heq _ HEq.rfl).symm).trans
      (((rec_heq_of_heq _ HEq.rfl).symm).trans
        ((heq_of_eq hpspr).trans (rec_heq_of_heq _ HEq.rfl)))
  exact h1'.trans ((rec_heq_of_heq
    (C := fun v => Act i (O.currentObs i v))
    (x := π' i (O.projectStates i ss'))
    (y := π' i (O.projectStates i ss'))
    hobs_i.symm HEq.rfl).symm)

/-- Per-player version of `pureStep_component_eq_of_pspr`:
only needs `PlayerStepRecall O i` for the specific player `i`,
not the full `PerStepPlayerRecall` for all players. -/
theorem pureStep_component_eq_of_playerRecall
    (i : ι) (hPSR_i : PlayerStepRecall O i) {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hobs_i : O.projectStates i ss = O.projectStates i ss')
    (hobst_i : O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0) :
    π i (O.projectStates i ss) = hobs_i ▸ π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  have hpspr := hPSR_i.action_eq h1 h2
    (O.obsEq_of_projectStates_getLast i hobs_i) hobst_i
  apply eq_of_heq
  have h1' : HEq (π i (O.projectStates i ss)) (π' i (O.projectStates i ss')) :=
    ((rec_heq_of_heq _ HEq.rfl).symm).trans
      (((rec_heq_of_heq _ HEq.rfl).symm).trans
        ((heq_of_eq hpspr).trans (rec_heq_of_heq _ HEq.rfl)))
  exact h1'.trans ((rec_heq_of_heq
    (C := fun v => Act i (O.currentObs i v))
    (x := π' i (O.projectStates i ss'))
    (y := π' i (O.projectStates i ss'))
    hobs_i.symm HEq.rfl).symm)

end Decentralization

end ObsModel
