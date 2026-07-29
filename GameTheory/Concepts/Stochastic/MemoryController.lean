/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Adaptive
import Math.ProbabilityMassFunction

/-!
# Stochastic memory controllers for behavioral strategies

A stochastic account construction first describes a hidden memory state, an
action kernel conditional on that memory, and a memory update after the realized
action and next state. The stochastic-game API, however, quantifies over
ordinary behavioral strategies indexed only by game histories.

This file gives the canonical posterior construction. At a game history, the
controller keeps the conditional law of its memory, mixes the memory-dependent
action kernels, and after an observed action reweights the memory law by that
action's likelihood before applying the stochastic memory update. The resulting
behavioral strategy depends only on the observed game history.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type}

/-- Probability of a tagged pair produced by two successive finite PMF
kernels. -/
theorem bind_tag_apply {A B : Type*} [Finite A] [Finite B]
    (p : PMF A) (q : A → PMF B) (a : A) (b : B) :
    (p.bind (fun a' =>
      (q a').bind (fun b' => PMF.pure (a', b')))) (a, b) =
      p a * q a b := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  simp only [PMF.bind_apply, tsum_fintype, PMF.pure_apply]
  calc
    _ = ∑ a' : A, if a = a' then p a' * q a' b else 0 := by
      apply Finset.sum_congr rfl
      intro a' _
      by_cases ha : a = a'
      · subst a'
        simp
      · simp [ha]
    _ = p a * q a b := by simp

private theorem reweight_update_weighted_eq
    {M A M' : Type*} [Fintype M]
    (μ : PMF M) (select : M → PMF A) (update : M → A → PMF M')
    (a : A) (b : M') :
    (μ.bind select) a *
        ((reweightPMF μ (fun m => select m a)).bind
          (fun m => update m a)) b =
      ∑ m : M, μ m * (select m a * update m a b) := by
  classical
  have hZ :
      (μ.bind select) a = ∑ m : M, μ m * select m a := by
    simp [PMF.bind_apply, tsum_fintype]
  rw [hZ]
  by_cases hZ0 : (∑ m : M, μ m * select m a) = 0
  · have hterm : ∀ m, μ m * select m a = 0 :=
      fun m => (ENNReal.tsum_eq_zero.mp (by rwa [tsum_fintype])) m
    rw [hZ0, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro m _
    rw [← mul_assoc, hterm m, zero_mul]
  have hZtop : (∑ m : M, μ m * select m a) ≠ ⊤ := by
    rw [← hZ]
    exact PMF.apply_ne_top (μ.bind select) a
  rw [PMF.bind_apply, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [reweightPMF_apply μ _ m hZ0 hZtop, div_eq_mul_inv]
  rw [← mul_assoc, ← mul_assoc (∑ _, _)]
  rw [mul_comm (∑ _, _) (μ m * _)]
  rw [mul_assoc (μ m * _) (∑ _, _)]
  rw [ENNReal.mul_inv_cancel hZ0 hZtop, mul_one, mul_assoc]

/-- Bayes recomposition for a finite hidden memory. Sampling a memory, then
an action, then the next memory has the same tagged action/next-memory law as
sampling the mixed action first, reweighting the old memory by that action's
likelihood, and applying the memory update. The zero-likelihood fallback of
`reweightPMF` is harmless because the corresponding mixed action has zero
mass. -/
theorem bind_select_reweight_update_tagged
    {M A M' : Type*} [Fintype M] [Finite A] [Finite M']
    (μ : PMF M) (select : M → PMF A) (update : M → A → PMF M') :
    μ.bind (fun m =>
      (select m).bind (fun a =>
        (update m a).bind (fun m' => PMF.pure (a, m')))) =
      (μ.bind select).bind (fun a =>
        (reweightPMF μ (fun m => select m a)).bind (fun m =>
          (update m a).bind (fun m' => PMF.pure (a, m')))) := by
  classical
  ext z
  rcases z with ⟨a, b⟩
  calc
    (μ.bind (fun m =>
        (select m).bind (fun a =>
          (update m a).bind (fun m' => PMF.pure (a, m'))))) (a, b) =
        ∑ m : M, μ m * (select m a * update m a b) := by
      rw [PMF.bind_apply, tsum_fintype]
      apply Finset.sum_congr rfl
      intro m _
      rw [bind_tag_apply]
    _ = (μ.bind select) a *
          ((reweightPMF μ (fun m => select m a)).bind
            (fun m => update m a)) b :=
      (reweight_update_weighted_eq μ select update a b).symm
    _ = ((μ.bind select).bind (fun a =>
        (reweightPMF μ (fun m => select m a)).bind (fun m =>
          (update m a).bind (fun m' => PMF.pure (a, m'))))) (a, b) := by
      symm
      calc
        _ = ((μ.bind select).bind (fun a =>
            ((reweightPMF μ (fun m => select m a)).bind
              (fun m => update m a)).bind
                (fun m' => PMF.pure (a, m')))) (a, b) := by
          congr 2
          funext a
          rw [PMF.bind_bind]
        _ = _ := bind_tag_apply _ _ _ _

/-- Bayes recomposition when the outcome likelihood factors into a
memory-independent term and a memory-dependent personal-action term. Only the
personal term is needed in the posterior. This is the cancellation that makes
the controller posterior independent of the opponents' strategy and of the
game's transition probability. -/
theorem bind_select_factor_reweight_update_tagged
    {M A M' : Type*} [Fintype M] [Finite A] [Finite M']
    (μ : PMF M) (select : M → PMF A)
    (personal : M → A → ENNReal) (common : A → ENNReal)
    (update : M → A → PMF M')
    (hfactor : ∀ m a, select m a = common a * personal m a)
    (hcommonTop : ∀ a, common a ≠ ⊤) :
    μ.bind (fun m =>
      (select m).bind (fun a =>
        (update m a).bind (fun m' => PMF.pure (a, m')))) =
      (μ.bind select).bind (fun a =>
        (reweightPMF μ (fun m => personal m a)).bind (fun m =>
          (update m a).bind (fun m' => PMF.pure (a, m')))) := by
  rw [bind_select_reweight_update_tagged]
  apply bind_congr_on_support
  intro a ha
  have hcommon0 : common a ≠ 0 := by
    intro hzero
    have hselectZero : ∀ m, select m a = 0 := by
      intro m
      rw [hfactor m a, hzero, zero_mul]
    have houtZero : (μ.bind select) a = 0 := by
      simp [PMF.bind_apply, hselectZero]
    have houtNonzero : (μ.bind select) a ≠ 0 := by
      simpa [PMF.mem_support_iff] using ha
    exact houtNonzero houtZero
  have hreweight :
      reweightPMF μ (fun m => select m a) =
        reweightPMF μ (fun m => personal m a) := by
    rw [show (fun m => select m a) =
        (fun m => common a * personal m a) by
      funext m
      exact hfactor m a]
    exact reweightPMF_scale μ (fun m => personal m a)
      (common a) hcommon0 (hcommonTop a)
  rw [hreweight]

/-- A history-based controller with a finite memory type at each depth.
Allowing the type to depend on the depth covers counters whose reachable range
grows with the length of the history. -/
structure MemoryController (G : StochasticGame ι) (who : ι) where
  /-- Memory states reachable at each decision depth. -/
  Mem : ℕ → Type
  /-- Each finite history has only finitely many reachable memory states. -/
  finiteMem : ∀ t, Fintype (Mem t)
  /-- Initial memory law. -/
  initial : PMF (Mem 0)
  /-- Action law at a history and memory state. -/
  select : ∀ t, G.Hist t → Mem t → PMF (G.Act who)
  /-- Memory update after observing the joint action and next state. -/
  update :
    ∀ t, G.Hist t → G.JointAct → G.State → Mem t → PMF (Mem (t + 1))

/-- Remove the final completed stage from a nonempty history. -/
def historyPrefix (G : StochasticGame ι) {t : ℕ}
    (h : G.Hist (t + 1)) : G.Hist t :=
  (Fin.init h.1, (h.1 (Fin.last t)).1)

/-- Joint action in the final completed stage of a nonempty history. -/
def historyLastAction (G : StochasticGame ι) {t : ℕ}
    (h : G.Hist (t + 1)) : G.JointAct :=
  (h.1 (Fin.last t)).2

@[simp] theorem historyPrefix_snoc
    (G : StochasticGame ι) {t : ℕ} (h : G.Hist t)
    (a : G.JointAct) (s' : G.State) :
    G.historyPrefix ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1)) = h := by
  simp [historyPrefix]

@[simp] theorem historyLastAction_snoc
    (G : StochasticGame ι) {t : ℕ} (h : G.Hist t)
    (a : G.JointAct) (s' : G.State) :
    G.historyLastAction
        ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1)) = a := by
  simp [historyLastAction]

/-- Posterior law of the controller memory after an observed game history.
The update is independent of the opponents' strategy: their action likelihood
and the game transition probability are common to every candidate memory and
cancel from Bayes' rule. On a zero-likelihood history, `reweightPMF` uses its
documented fallback; such histories have no effect on induced expectations. -/
noncomputable def MemoryController.belief
    {G : StochasticGame ι} {who : ι} (C : G.MemoryController who) :
    (t : ℕ) → G.Hist t → PMF (C.Mem t)
  | 0, _ => C.initial
  | t + 1, h' =>
      let h := G.historyPrefix h'
      let a := G.historyLastAction h'
      letI : Fintype (C.Mem t) := C.finiteMem t
      (reweightPMF (C.belief t h)
        (fun m => C.select t h m (a who))).bind
          (fun m => C.update t h a h'.2 m)

@[simp] theorem MemoryController.belief_zero
    {G : StochasticGame ι} {who : ι} (C : G.MemoryController who)
    (h : G.Hist 0) :
    C.belief 0 h = C.initial :=
  rfl

theorem MemoryController.belief_succ
    {G : StochasticGame ι} {who : ι} (C : G.MemoryController who)
    {t : ℕ} (h' : G.Hist (t + 1)) :
    C.belief (t + 1) h' =
      let h := G.historyPrefix h'
      let a := G.historyLastAction h'
      letI : Fintype (C.Mem t) := C.finiteMem t
      (reweightPMF (C.belief t h)
        (fun m => C.select t h m (a who))).bind
          (fun m => C.update t h a h'.2 m) :=
  rfl

/-- The ordinary behavioral strategy induced by a stochastic memory
controller: mix its action kernels under the posterior memory law. -/
noncomputable def MemoryController.behaviorStrategy
    {G : StochasticGame ι} {who : ι} (C : G.MemoryController who) :
    G.BehaviorStrategy who :=
  fun t h => (C.belief t h).bind (C.select t h)

@[simp] theorem MemoryController.behaviorStrategy_apply
    {G : StochasticGame ι} {who : ι} (C : G.MemoryController who)
    (t : ℕ) (h : G.Hist t) :
    C.behaviorStrategy t h =
      (C.belief t h).bind (C.select t h) :=
  rfl

/-- Joint-action/next-state law at a fixed history and memory state, with the
controlled player's component replaced by the controller's selected action
law. -/
noncomputable def MemoryController.outcomeKernel
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    {who : ι} (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t) :
    PMF (G.JointAct × G.State) :=
  (G.stageActionDist
      (Function.update opp who (fun _ _ => C.select t h m)) h).bind
    (fun a => (G.transition h.2 a).bind
      (fun s' => PMF.pure (a, s')))

/-- Joint-action/next-state law generated by the controller's induced
ordinary behavioral strategy. -/
noncomputable def MemoryController.behaviorOutcomeKernel
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    {who : ι} (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) :
    PMF (G.JointAct × G.State) :=
  (G.stageActionDist
      (Function.update opp who C.behaviorStrategy) h).bind
    (fun a => (G.transition h.2 a).bind
      (fun s' => PMF.pure (a, s')))

/-- The outcome likelihood factors into the controller action likelihood and
a memory-independent product of the opponents' action likelihoods and the
state-transition likelihood. -/
theorem MemoryController.outcomeKernel_apply
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] [Finite G.State]
    {who : ι} (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t)
    (a : G.JointAct) (s' : G.State) :
    C.outcomeKernel opp h m (a, s') =
      ((∏ i ∈ Finset.univ.erase who, opp i t h (a i)) *
          G.transition h.2 a s') *
        C.select t h m (a who) := by
  letI : ∀ i, Fintype (G.Act i) :=
    fun i => Fintype.ofFinite (G.Act i)
  letI : Fintype G.State := Fintype.ofFinite G.State
  rw [MemoryController.outcomeKernel, bind_tag_apply]
  unfold stageActionDist
  have hprofile :
      (fun i =>
        (Function.update opp who (fun _ _ => C.select t h m)) i t h) =
        Function.update (fun i => opp i t h) who (C.select t h m) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  rw [hprofile]
  rw [pmfPi_apply_update_family]
  ring

/-- Mixing the memory-conditional outcome kernels under the posterior belief
is exactly the action/next-state law generated by the induced behavioral
strategy. -/
theorem MemoryController.bind_belief_outcomeKernel
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] [Finite G.State]
    {who : ι} (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) :
    (C.belief t h).bind (C.outcomeKernel opp h) =
      C.behaviorOutcomeKernel opp h := by
  letI : ∀ i, Fintype (G.Act i) :=
    fun i => Fintype.ofFinite (G.Act i)
  letI : Fintype G.State := Fintype.ofFinite G.State
  let k : G.Act who → PMF (G.JointAct × G.State) := fun ai =>
    (pmfPi
      (Function.update (fun i => opp i t h) who (PMF.pure ai))).bind
        (fun a => (G.transition h.2 a).bind
          (fun s' => PMF.pure (a, s')))
  have houtcome : ∀ m,
      C.outcomeKernel opp h m =
        (C.select t h m).bind k := by
    intro m
    unfold MemoryController.outcomeKernel stageActionDist
    have hprofile :
        (fun i =>
          (Function.update opp who (fun _ _ => C.select t h m)) i t h) =
          Function.update (fun i => opp i t h) who (C.select t h m) := by
      funext i
      by_cases hi : i = who
      · subst i
        simp
      · simp [Function.update_of_ne hi]
    rw [hprofile, pmfPi_update_bind, PMF.bind_bind]
  have hbehavior :
      C.behaviorOutcomeKernel opp h =
        (C.behaviorStrategy t h).bind k := by
    unfold MemoryController.behaviorOutcomeKernel stageActionDist
    have hprofile :
        (fun i =>
          (Function.update opp who C.behaviorStrategy) i t h) =
          Function.update (fun i => opp i t h) who
            (C.behaviorStrategy t h) := by
      funext i
      by_cases hi : i = who
      · subst i
        simp
      · simp [Function.update_of_ne hi]
    rw [hprofile, pmfPi_update_bind, PMF.bind_bind]
  calc
    (C.belief t h).bind (C.outcomeKernel opp h) =
        (C.belief t h).bind
          (fun m => (C.select t h m).bind k) := by
            congr 1
            funext m
            exact houtcome m
    _ = ((C.belief t h).bind (C.select t h)).bind k := by
      rw [PMF.bind_bind]
    _ = (C.behaviorStrategy t h).bind k := by
      rw [C.behaviorStrategy_apply]
    _ = C.behaviorOutcomeKernel opp h := hbehavior.symm

/-- One-step realization of the hidden-memory update. Starting from the
posterior memory law, sampling memory before the action gives the same tagged
outcome/next-memory law as sampling the mixed outcome first and then using the
posterior attached to the extended game history. -/
theorem MemoryController.belief_outcome_update_tagged
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] [Finite G.State]
    {who : ι} (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) :
    (C.belief t h).bind (fun m =>
      (C.outcomeKernel opp h m).bind (fun o =>
        (C.update t h o.1 o.2 m).bind
          (fun m' => PMF.pure (o, m')))) =
      ((C.belief t h).bind (C.outcomeKernel opp h)).bind (fun o =>
        (C.belief (t + 1)
          (Fin.snoc h.1 (h.2, o.1), o.2)).bind
            (fun m' => PMF.pure (o, m'))) := by
  letI : ∀ i, Fintype (G.Act i) :=
    fun i => Fintype.ofFinite (G.Act i)
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : Fintype (C.Mem t) := C.finiteMem t
  letI : Fintype (C.Mem (t + 1)) := C.finiteMem (t + 1)
  let personal : C.Mem t → (G.JointAct × G.State) → ENNReal :=
    fun m o => C.select t h m (o.1 who)
  let common : (G.JointAct × G.State) → ENNReal :=
    fun o =>
      (∏ i ∈ Finset.univ.erase who, opp i t h (o.1 i)) *
        G.transition h.2 o.1 o.2
  have hfactor : ∀ m o,
      C.outcomeKernel opp h m o = common o * personal m o := by
    rintro m ⟨a, s'⟩
    exact C.outcomeKernel_apply opp h m a s'
  have hcommonTop : ∀ o, common o ≠ ⊤ := by
    rintro ⟨a, s'⟩
    apply ENNReal.mul_ne_top
    · exact ENNReal.prod_ne_top fun i _ =>
        PMF.apply_ne_top (opp i t h) (a i)
    · exact PMF.apply_ne_top (G.transition h.2 a) s'
  have hbayes :=
    bind_select_factor_reweight_update_tagged
      (C.belief t h) (C.outcomeKernel opp h)
      personal common (fun m o => C.update t h o.1 o.2 m)
      hfactor hcommonTop
  simpa [personal, MemoryController.belief] using hbayes

/-- One-step controller realization stated entirely with the outcome law of
the induced ordinary behavioral strategy. Its successor belief is therefore
the genuine conditional memory law along every supported extended history. -/
theorem MemoryController.behaviorOutcome_belief_succ_tagged
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] [Finite G.State]
    {who : ι} (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) :
    (C.behaviorOutcomeKernel opp h).bind (fun o =>
      (C.belief (t + 1)
        (Fin.snoc h.1 (h.2, o.1), o.2)).bind
          (fun m' => PMF.pure (o, m'))) =
      (C.belief t h).bind (fun m =>
        (C.outcomeKernel opp h m).bind (fun o =>
          (C.update t h o.1 o.2 m).bind
            (fun m' => PMF.pure (o, m')))) := by
  rw [← C.bind_belief_outcomeKernel opp h]
  exact (C.belief_outcome_update_tagged opp h).symm

end StochasticGame
end GameTheory
