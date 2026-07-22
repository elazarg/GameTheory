/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Theorems
import GameTheory.Languages.EFG.Refinements
import GameTheory.Languages.EFG.OneShotDeviation

/-!
# Two-Stage Open Games as Extensive-Form Games

This bridge preserves the sequential structure of `OpenGames.ShapeS`.  The
leader has one information set and the follower has one information set for
each observed leader action.  Consequently, an EFG pure strategy profile is
equivalent to a leader action paired with a contingent follower plan.

This is deliberately different from routing the compiled strategic form
through the NFG-to-EFG bridge: that encoding makes the moves simultaneous and
therefore cannot express the subgames needed for subgame perfection.
-/

noncomputable section

namespace OpenGames.ShapeS

open GameTheory
open EFG

/- The `Fintype` constraints below are inherited from `InfoStructure.arity`:
EFG actions are encoded by finite arities, rather than by arbitrary action
carriers. -/
variable (A B : Type) [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B]

/-- The perfect-information information structure for a two-stage shape.
Player `0` moves once; player `1` observes that action before moving. -/
@[reducible] def efgInfo (A B : Type) [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] : InfoStructure where
  n := 2
  Infoset := Fin.cases Unit (fun _ => A)
  fInfo := fun p => by
    refine Fin.cases ?_ (fun _ => ?_) p
    · change Fintype Unit
      infer_instance
    · change Fintype A
      infer_instance
  dInfo := fun p => by
    refine Fin.cases ?_ (fun _ => ?_) p
    · change DecidableEq Unit
      infer_instance
    · change DecidableEq A
      infer_instance
  arity := Fin.cases (fun _ => Fintype.card A) (fun _ _ => Fintype.card B)
  arity_pos := Fin.cases (fun _ => Fintype.card_pos) (fun _ _ => Fintype.card_pos)

/-- Decode the EFG's finite action representation. -/
def decodeAction (T : Type) [Fintype T] [DecidableEq T] [Nonempty T] :
    Fin (Fintype.card T) ≃ T :=
  (Fintype.equivFin T).symm

/-- The leader's unique information set. -/
def leaderInfo : (efgInfo A B).Infoset (0 : Fin 2) := by
  change Unit
  exact ()

/-- The follower information set reached after leader action `a`. -/
def followerInfo (a : A) : (efgInfo A B).Infoset (Fin.succ 0 : Fin 2) := by
  change A
  exact a

/-- The staged EFG tree: the follower's information-set identifier is the
observed leader action. -/
def efgTree : GameTree (efgInfo A B) (A × B) :=
  .decision (p := (0 : Fin 2)) (leaderInfo A B) fun a =>
    let leaderAction := decodeAction A a
    .decision (p := (Fin.succ 0 : Fin 2)) (followerInfo A B leaderAction) fun b =>
      .terminal (leaderAction, decodeAction B b)

/-- Compile a two-stage open-game shape directly to a perfect-information
extensive-form game. -/
@[reducible] def toEFG (k : A × B → ℝ × ℝ) : EFGGame where
  inf := efgInfo A B
  Outcome := A × B
  tree := efgTree A B
  utility outcome p := Fin.cases (k outcome).1
    (fun _ : Fin 1 => (k outcome).2) p

/-- Translate a leader action and contingent follower plan to an EFG pure
strategy profile. -/
def toPureProfile (σ : A × (A → B)) : PureProfile (efgInfo A B) :=
  fun p => Fin.cases
    (fun _ => (decodeAction A).symm σ.1)
    (fun _ a => (decodeAction B).symm (σ.2 a)) p

/-- Read a two-stage contingent plan from an EFG pure profile. -/
def ofPureProfile (σ : PureProfile (efgInfo A B)) : A × (A → B) :=
  (decodeAction A (σ 0 (leaderInfo A B)),
    fun a => decodeAction B (σ (Fin.succ 0) (followerInfo A B a)))

@[simp] theorem toPureProfile_leader (σ : A × (A → B)) :
    toPureProfile A B σ 0 (leaderInfo A B) =
      (decodeAction A).symm σ.1 := rfl

@[simp] theorem toPureProfile_follower (σ : A × (A → B)) (a : A) :
    toPureProfile A B σ (Fin.succ 0) (followerInfo A B a) =
      (decodeAction B).symm (σ.2 a) := rfl

/-- Two-stage open-game strategies and EFG pure profiles are equivalent. -/
def pureProfileEquiv :
    (A × (A → B)) ≃ PureProfile (efgInfo A B) where
  toFun := toPureProfile A B
  invFun := ofPureProfile A B
  left_inv σ := by
    apply Prod.ext
    · change decodeAction A (toPureProfile A B σ 0 (leaderInfo A B)) = σ.1
      rw [toPureProfile_leader, (decodeAction A).apply_symm_apply]
    · funext a
      change decodeAction B
        (toPureProfile A B σ (Fin.succ 0) (followerInfo A B a)) = σ.2 a
      rw [toPureProfile_follower,
        (decodeAction B).apply_symm_apply]
  right_inv σ := by
    funext p I
    fin_cases p
    · cases I
      change toPureProfile A B (ofPureProfile A B σ) 0 (leaderInfo A B) =
        σ 0 (leaderInfo A B)
      rw [toPureProfile_leader]
      exact (decodeAction A).symm_apply_apply (σ 0 (leaderInfo A B))
    · change A at I
      change toPureProfile A B (ofPureProfile A B σ) (Fin.succ 0)
          (followerInfo A B I) = σ (Fin.succ 0) (followerInfo A B I)
      rw [toPureProfile_follower]
      exact (decodeAction B).symm_apply_apply
        (σ (Fin.succ 0) (followerInfo A B I))

/-- Realized staged outcome of an EFG contingent plan. -/
def realizedOutcome (σ : PureProfile (efgInfo A B)) : A × B :=
  let plan := ofPureProfile A B σ
  (plan.1, plan.2 plan.1)

/-- Evaluating a staged tree reads exactly the realized components exposed by
`ofPureProfile`. -/
theorem efgTree_evalPure_eq_ofPureProfile
    (σ : PureProfile (efgInfo A B)) :
    (efgTree A B).evalPure σ = realizedOutcome A B σ := by
  rfl

/-- The staged tree contains no chance nodes. -/
theorem efgTree_isDeterministic : IsDeterministic (efgTree A B) := by
  unfold efgTree
  apply IsDeterministic.decision
  intro a
  apply IsDeterministic.decision
  intro b
  exact .terminal _

/-- Pure EFG evaluation agrees with the open-game play map. -/
@[simp] theorem efgTree_evalPure (σ : A × (A → B)) :
    (efgTree A B).evalPure (toPureProfile A B σ) = (σ.1, σ.2 σ.1) := by
  rw [efgTree_evalPure_eq_ofPureProfile]
  have h := (pureProfileEquiv A B).left_inv σ
  change ofPureProfile A B (toPureProfile A B σ) = σ at h
  simp only [realizedOutcome]
  rw [h]

/-- Distributional evaluation is the point mass at the open-game play. -/
theorem efgTree_evalDist (σ : A × (A → B)) :
    (efgTree A B).evalDist (pureToBehavioral (toPureProfile A B σ)) =
      PMF.pure (σ.1, σ.2 σ.1) := by
  rw [evalDist_pureToBehavioral_eq_pure _ _ (efgTree_isDeterministic A B)]
  rw [efgTree_evalPure]

/-- The EFG strategic kernel and the direct `ShapeS` strategic compilation
produce the same outcome law under their respective profile translations. -/
theorem toEFG_outcomeKernel_eq_compileAction
    (k : A × B → ℝ × ℝ) (σ : A × (A → B)) :
    (toEFG A B k).toStrategicKernelGame.outcomeKernel
        (toPureProfile A B σ) =
      (compileAction A B k).outcomeKernel (toProfile σ) := by
  change (efgTree A B).evalDist
      (pureToBehavioral (toPureProfile A B σ)) =
    PMF.pure (σ.1, σ.2 σ.1)
  exact efgTree_evalDist A B σ

/-- Distributional evaluation for an arbitrary EFG contingent plan. -/
theorem efgTree_evalDist_profile (σ : PureProfile (efgInfo A B)) :
    (efgTree A B).evalDist (pureToBehavioral σ) =
      PMF.pure (realizedOutcome A B σ) := by
  rw [evalDist_pureToBehavioral_eq_pure _ _ (efgTree_isDeterministic A B)]
  rw [efgTree_evalPure_eq_ofPureProfile]

/-- The follower subgame after observed action `a`. -/
def efgFollowerTree (a : A) : GameTree (efgInfo A B) (A × B) :=
  .decision (p := (Fin.succ 0 : Fin 2)) (followerInfo A B a) fun b =>
    .terminal (a, decodeAction B b)

theorem efgFollowerTree_isDeterministic (a : A) :
    IsDeterministic (efgFollowerTree A B a) := by
  unfold efgFollowerTree
  apply IsDeterministic.decision
  intro b
  exact .terminal _

theorem efgFollowerTree_evalDist_profile (a : A)
    (σ : PureProfile (efgInfo A B)) :
    (efgFollowerTree A B a).evalDist (pureToBehavioral σ) =
      PMF.pure (a, decodeAction B
        (σ (Fin.succ 0) (followerInfo A B a))) := by
  rw [evalDist_pureToBehavioral_eq_pure _ _
    (efgFollowerTree_isDeterministic A B a)]
  rfl

@[simp] theorem realizedOutcome_toPureProfile (σ : A × (A → B)) :
    realizedOutcome A B (toPureProfile A B σ) = (σ.1, σ.2 σ.1) := by
  have h := (pureProfileEquiv A B).left_inv σ
  change ofPureProfile A B (toPureProfile A B σ) = σ at h
  simp only [realizedOutcome]
  rw [h]

/-- Replacing the leader's EFG strategy changes only the leader component of
the decoded contingent plan. -/
theorem ofPureProfile_update_leader (σ : PureProfile (efgInfo A B))
    (s' : PureStrategy (efgInfo A B) 0) :
    ofPureProfile A B (Function.update σ 0 s') =
      (decodeAction A (s' (leaderInfo A B)), (ofPureProfile A B σ).2) := by
  apply Prod.ext
  · simp [ofPureProfile]
  · funext a
    simp [ofPureProfile, Function.update]

/-- Replacing the follower's EFG strategy changes the entire contingent
follower plan and leaves the leader action fixed. -/
theorem ofPureProfile_update_follower (σ : PureProfile (efgInfo A B))
    (s' : PureStrategy (efgInfo A B) (Fin.succ 0)) :
    ofPureProfile A B (Function.update σ (Fin.succ 0) s') =
      ((ofPureProfile A B σ).1,
        fun a => decodeAction B (s' (followerInfo A B a))) := by
  apply Prod.ext
  · simp [ofPureProfile, Function.update]
  · funext a
    simp [ofPureProfile]

@[simp] theorem realizedOutcome_update_leader (σ : A × (A → B))
    (s' : PureStrategy (efgInfo A B) 0) :
    realizedOutcome A B (Function.update (toPureProfile A B σ) 0 s') =
      let a := decodeAction A (s' (leaderInfo A B))
      (a, σ.2 a) := by
  rw [realizedOutcome]
  rw [ofPureProfile_update_leader]
  have h := (pureProfileEquiv A B).left_inv σ
  change ofPureProfile A B (toPureProfile A B σ) = σ at h
  rw [h]

@[simp] theorem realizedOutcome_update_follower (σ : A × (A → B))
    (s' : PureStrategy (efgInfo A B) (Fin.succ 0)) :
    realizedOutcome A B
        (Function.update (toPureProfile A B σ) (Fin.succ 0) s') =
      (σ.1, decodeAction B (s' (followerInfo A B σ.1))) := by
  rw [realizedOutcome]
  rw [ofPureProfile_update_follower]
  have h := (pureProfileEquiv A B).left_inv σ
  change ofPureProfile A B (toPureProfile A B σ) = σ at h
  rw [h]

/-- Expected utility at the root is utility of the realized staged outcome. -/
theorem toEFG_root_eu (k : A × B → ℝ × ℝ)
    (σ : PureProfile (efgInfo A B)) (p : Fin 2) :
    (toEFG A B k).toStrategicKernelGame.eu σ p =
      Fin.cases (k (realizedOutcome A B σ)).1
        (fun _ : Fin 1 => (k (realizedOutcome A B σ)).2) p := by
  unfold toEFG
  simp only [KernelGame.eu, EFGGame.toStrategicKernelGame]
  rw [efgTree_evalDist_profile]
  simp

/-- Expected utility in a follower subgame. -/
theorem toEFG_follower_eu (k : A × B → ℝ × ℝ) (a : A)
    (σ : PureProfile (efgInfo A B)) (p : Fin 2) :
    ((toEFG A B k).withTree (efgFollowerTree A B a)).toStrategicKernelGame.eu σ p =
      Fin.cases
        (k (a, decodeAction B (σ (Fin.succ 0) (followerInfo A B a)))).1
        (fun _ : Fin 1 =>
          (k (a, decodeAction B (σ (Fin.succ 0) (followerInfo A B a)))).2) p := by
  unfold toEFG
  simp only [KernelGame.eu, EFGGame.toStrategicKernelGame, EFGGame.withTree]
  rw [efgFollowerTree_evalDist_profile]
  simp

theorem toEFG_root_eu_update_leader (k : A × B → ℝ × ℝ)
    (σ : A × (A → B)) (s' : PureStrategy (efgInfo A B) 0) :
    (toEFG A B k).toStrategicKernelGame.eu
        (Function.update (toPureProfile A B σ) 0 s') 0 =
      (k (decodeAction A (s' (leaderInfo A B)),
        σ.2 (decodeAction A (s' (leaderInfo A B))))).1 := by
  change Math.Probability.expect
      ((efgTree A B).evalDist (pureToBehavioral
        (Function.update (toPureProfile A B σ) 0 s')))
      (fun outcome => (k outcome).1) = _
  rw [efgTree_evalDist_profile]
  simp only [Math.Probability.expect_pure]
  rw [realizedOutcome_update_leader]

theorem toEFG_root_eu_update_follower (k : A × B → ℝ × ℝ)
    (σ : A × (A → B))
    (s' : PureStrategy (efgInfo A B) (Fin.succ 0)) :
    (toEFG A B k).toStrategicKernelGame.eu
        (Function.update (toPureProfile A B σ) (Fin.succ 0) s') (Fin.succ 0) =
      (k (σ.1, decodeAction B (s' (followerInfo A B σ.1)))).2 := by
  change Math.Probability.expect
      ((efgTree A B).evalDist (pureToBehavioral
        (Function.update (toPureProfile A B σ) (Fin.succ 0) s')))
      (fun outcome => (k outcome).2) = _
  rw [efgTree_evalDist_profile]
  simp only [Math.Probability.expect_pure]
  rw [realizedOutcome_update_follower]

theorem toEFG_follower_eu_obedient (k : A × B → ℝ × ℝ)
    (σ : A × (A → B)) (a : A) :
    ((toEFG A B k).withTree
      (efgFollowerTree A B a)).toStrategicKernelGame.eu
        (toPureProfile A B σ) (Fin.succ 0) = (k (a, σ.2 a)).2 := by
  rw [toEFG_follower_eu]
  simp only [Fin.cases_succ]
  rw [toPureProfile_follower, (decodeAction B).apply_symm_apply]

theorem toEFG_follower_eu_update (k : A × B → ℝ × ℝ)
    (σ : A × (A → B)) (a : A)
    (s' : PureStrategy (efgInfo A B) (Fin.succ 0)) :
    ((toEFG A B k).withTree
      (efgFollowerTree A B a)).toStrategicKernelGame.eu
        (Function.update (toPureProfile A B σ) (Fin.succ 0) s') (Fin.succ 0) =
      (k (a, decodeAction B (s' (followerInfo A B a)))).2 := by
  change Math.Probability.expect
      ((efgFollowerTree A B a).evalDist (pureToBehavioral
        (Function.update (toPureProfile A B σ) (Fin.succ 0) s')))
      (fun outcome => (k outcome).2) = _
  rw [efgFollowerTree_evalDist_profile]
  simp only [Math.Probability.expect_pure, Function.update_self]

/-- The intrinsic conditioned inequalities make the translated profile Nash
at the root strategic form. -/
theorem conditioned_root_isNash
    (k : A × B → ℝ × ℝ) (σ : A × (A → B))
    (h : (conditioned A B).IsEquilibriumIn () k σ) :
    (toEFG A B k).toStrategicKernelGame.IsNash (toPureProfile A B σ) := by
  intro who
  refine Fin.cases ?_ (fun q => ?_) who
  · intro s'
    change PureStrategy (efgInfo A B) 0 at s'
    rw [toEFG_root_eu, toEFG_root_eu_update_leader]
    simp only [realizedOutcome_toPureProfile, Fin.cases_zero]
    exact h.1 (decodeAction A (s' (leaderInfo A B)))
  · have hq : q = 0 := Subsingleton.elim _ _
    subst q
    intro s'
    change PureStrategy (efgInfo A B) (Fin.succ 0) at s'
    rw [toEFG_root_eu, toEFG_root_eu_update_follower]
    simp only [realizedOutcome_toPureProfile, Fin.cases_succ]
    exact h.2 σ.1 (decodeAction B (s' (followerInfo A B σ.1)))

/-- The conditioned follower inequality is Nash in every follower subgame. -/
theorem conditioned_follower_isNashFor
    (k : A × B → ℝ × ℝ) (σ : A × (A → B))
    (h : (conditioned A B).IsEquilibriumIn () k σ) (a : A) :
    ((toEFG A B k).withTree (efgFollowerTree A B a)).toStrategicKernelGame.IsNashFor
      (KernelGame.euPref (toEFG A B k).toStrategicKernelGame)
      (toPureProfile A B σ) := by
  change ((toEFG A B k).withTree
    (efgFollowerTree A B a)).toStrategicKernelGame.IsNashFor
      (KernelGame.euPref ((toEFG A B k).withTree
        (efgFollowerTree A B a)).toStrategicKernelGame) (toPureProfile A B σ)
  rw [← KernelGame.IsNash_iff_IsNashFor_eu]
  intro who
  refine Fin.cases ?_ (fun q => ?_) who
  · intro s'
    rw [toEFG_follower_eu, toEFG_follower_eu]
    simp [Function.update]
  · have hq : q = 0 := Subsingleton.elim _ _
    subst q
    intro s'
    rw [toEFG_follower_eu, toEFG_follower_eu]
    unfold toEFG at s' ⊢
    change PureStrategy (efgInfo A B) (Fin.succ 0) at s'
    rw [toPureProfile_follower]
    simp only [Function.update_self, Fin.cases_succ]
    rw [(decodeAction B).apply_symm_apply]
    exact h.2 a (decodeAction B (s' (followerInfo A B a)))

/-- Conditioned open-game equilibrium is subgame-perfect in the staged EFG. -/
theorem conditioned_implies_efg_isSubgamePerfectEq
    (k : A × B → ℝ × ℝ) (σ : A × (A → B))
    (h : (conditioned A B).IsEquilibriumIn () k σ) :
    (toEFG A B k).IsSubgamePerfectEq (toPureProfile A B σ) := by
  intro t hSub
  rcases hSub.1 with ⟨hist, hReach⟩
  change ReachBy hist (efgTree A B) t at hReach
  unfold efgTree at hReach
  cases hReach with
  | nil =>
      have hn := conditioned_root_isNash A B k σ h
      have hnFor := (KernelGame.IsNash_iff_IsNashFor_eu
        (toEFG A B k).toStrategicKernelGame (toPureProfile A B σ)).mp hn
      change (toEFG A B k).toStrategicKernelGame.IsNashFor
        (KernelGame.euPref (toEFG A B k).toStrategicKernelGame)
        (toPureProfile A B σ)
      exact hnFor
  | @cons step rest _ _ _ hstep hRest =>
      cases step with
      | chance n c =>
          simp [HistoryStepStep] at hstep
      | action p I a =>
          rcases hstep with ⟨next, hs, hu⟩
          cases hs
          subst hu
          cases hRest with
          | nil =>
              change ((toEFG A B k).withTree
                (efgFollowerTree A B (decodeAction A a))).toStrategicKernelGame.IsNashFor
                  (KernelGame.euPref (toEFG A B k).toStrategicKernelGame)
                  (toPureProfile A B σ)
              exact conditioned_follower_isNashFor A B k σ h (decodeAction A a)
          | @cons step' rest' _ _ _ hstep' hRest' =>
              cases step' with
              | chance n c =>
                  simp [HistoryStepStep] at hstep'
              | action p' I' b =>
                  rcases hstep' with ⟨next', hs', hu'⟩
                  cases hs'
                  subst hu'
                  cases hRest' with
                  | nil => exact terminal_isNashFor_euPref _ _
                  | @cons step'' _ _ _ _ hstep'' _ =>
                      cases step'' <;> simp [HistoryStepStep] at hstep''

/-- The staged encoding is perfect information: each leader action reaches a
distinct follower information set. -/
theorem efgTree_isPerfectInfo : IsPerfectInfo (efgTree A B) := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  unfold efgTree at hr₁ hr₂
  rcases ReachBy_decision_inv hr₁ with hroot₁ | ⟨a₁, rest₁, hh₁, hr₁'⟩
  · rcases hroot₁ with ⟨hh₁, hp₁, hI₁, hn₁⟩
    rcases ReachBy_decision_inv hr₂ with hroot₂ | ⟨a₂, rest₂, _hh₂, hr₂'⟩
    · rcases hroot₂ with ⟨hh₂, _hp₂, _hI₂, hn₂⟩
      exact ⟨hh₁.trans hh₂.symm, hn₁.symm.trans hn₂⟩
    · dsimp only at hr₂'
      rcases ReachBy_decision_inv hr₂' with hfollow₂ |
        ⟨b₂, rest₂', _hh₂', hterminal₂⟩
      · exact False.elim (by
          have hp₂ := hfollow₂.2.1
          exact Fin.succ_ne_zero 0 (hp₂.trans hp₁.symm))
      · exact False.elim (ReachBy_terminal_absurd hterminal₂)
  · dsimp only at hr₁'
    rcases ReachBy_decision_inv hr₁' with hfollow₁ |
      ⟨b₁, rest₁', _hh₁', hterminal₁⟩
    · rcases hfollow₁ with ⟨hrest₁, hp₁, hI₁, hn₁⟩
      rcases ReachBy_decision_inv hr₂ with hroot₂ | ⟨a₂, rest₂, hh₂, hr₂'⟩
      · exact False.elim (by
          have hp₂ := hroot₂.2.1
          exact Fin.succ_ne_zero 0 (hp₁.trans hp₂.symm))
      · dsimp only at hr₂'
        rcases ReachBy_decision_inv hr₂' with hfollow₂ |
          ⟨b₂, rest₂', _hh₂', hterminal₂⟩
        · rcases hfollow₂ with ⟨hrest₂, _hp₂, hI₂, hn₂⟩
          have hInfo : HEq
              (followerInfo A B (decodeAction A a₁))
              (followerInfo A B (decodeAction A a₂)) :=
            hI₁.trans hI₂.symm
          have haDecoded : decodeAction A a₁ = decodeAction A a₂ := by
            change HEq (decodeAction A a₁) (decodeAction A a₂) at hInfo
            exact eq_of_heq hInfo
          have ha : a₁ = a₂ := (decodeAction A).injective haDecoded
          subst a₂
          subst rest₁
          subst rest₂
          exact ⟨by simp [hh₁, hh₂], hn₁.symm.trans hn₂⟩
        · exact False.elim (ReachBy_terminal_absurd hterminal₂)
    · exact False.elim (ReachBy_terminal_absurd hterminal₁)

/-- EFG subgame perfection implies every intrinsic conditioned inequality. -/
theorem efg_isSubgamePerfectEq_implies_conditioned
    (k : A × B → ℝ × ℝ) (σ : A × (A → B))
    (h : (toEFG A B k).IsSubgamePerfectEq (toPureProfile A B σ)) :
    (conditioned A B).IsEquilibriumIn () k σ := by
  constructor
  · intro a
    have hn := spe_implies_isNash (toEFG A B k) (toPureProfile A B σ) h
    let s' : PureStrategy (efgInfo A B) 0 :=
      fun _ => (decodeAction A).symm a
    have hdev := hn 0 s'
    rw [toEFG_root_eu, toEFG_root_eu_update_leader] at hdev
    simp only [realizedOutcome_toPureProfile, Fin.cases_zero,
      s', (decodeAction A).apply_symm_apply] at hdev
    exact hdev
  · intro a b
    let chosen : Fin (Fintype.card A) := (decodeAction A).symm a
    have hReach : ReachBy
        [HistoryStep.action (0 : Fin 2) (leaderInfo A B) chosen]
        (efgTree A B) (efgFollowerTree A B a) := by
      have hchosen : decodeAction A chosen = a := by
        simp [chosen]
      have htail : ReachBy []
          (efgFollowerTree A B (decodeAction A chosen))
          (efgFollowerTree A B a) := by
        rw [hchosen]
        exact ReachBy.here _
      have hr := ReachBy.action (S := efgInfo A B)
        (p := (0 : Fin 2)) (I := leaderInfo A B)
        (next := fun move => efgFollowerTree A B (decodeAction A move))
        chosen htail
      simpa [efgTree, efgFollowerTree, chosen] using hr
    have hSub : IsSubgame (efgTree A B) (efgFollowerTree A B a) :=
      perfectInfo_isSubgame_decision (efgTree A B)
        (efgTree_isPerfectInfo A B) (followerInfo A B a)
        (fun move => .terminal (a, decodeAction B move)) hReach
    have hnFor := h (efgFollowerTree A B a) hSub
    change ((toEFG A B k).withTree
      (efgFollowerTree A B a)).toStrategicKernelGame.IsNashFor
        (KernelGame.euPref ((toEFG A B k).withTree
          (efgFollowerTree A B a)).toStrategicKernelGame)
        (toPureProfile A B σ) at hnFor
    have hn := (KernelGame.IsNash_iff_IsNashFor_eu
      ((toEFG A B k).withTree
        (efgFollowerTree A B a)).toStrategicKernelGame
      (toPureProfile A B σ)).mpr hnFor
    let s' : PureStrategy (efgInfo A B) (Fin.succ 0) :=
      fun _ => (decodeAction B).symm b
    have hdev := hn (Fin.succ 0) s'
    rw [toEFG_follower_eu_obedient, toEFG_follower_eu_update] at hdev
    simp only [s', (decodeAction B).apply_symm_apply] at hdev
    exact hdev

/-- Genuine Stage-2b correspondence: the conditioned two-stage open game is
equivalent to the library's concrete EFG subgame-perfect equilibrium. -/
theorem conditioned_isEquilibriumIn_iff_efg_isSubgamePerfectEq
    (k : A × B → ℝ × ℝ) (σ : A × (A → B)) :
    (conditioned A B).IsEquilibriumIn () k σ ↔
      (toEFG A B k).IsSubgamePerfectEq (toPureProfile A B σ) :=
  ⟨conditioned_implies_efg_isSubgamePerfectEq A B k σ,
    efg_isSubgamePerfectEq_implies_conditioned A B k σ⟩

/-- One-shot-deviation form of the same correspondence, obtained from the
library's finite perfect-information ODP theorem. -/
theorem conditioned_isEquilibriumIn_iff_hasNoOneShotDeviation
    (k : A × B → ℝ × ℝ) (σ : A × (A → B)) :
    (conditioned A B).IsEquilibriumIn () k σ ↔
      HasNoOneShotDeviation (toEFG A B k) (toPureProfile A B σ) := by
  rw [conditioned_isEquilibriumIn_iff_efg_isSubgamePerfectEq]
  exact oneShotDeviation_iff_spe (toEFG A B k) (toPureProfile A B σ)
    (efgTree_isPerfectInfo A B)

end OpenGames.ShapeS
