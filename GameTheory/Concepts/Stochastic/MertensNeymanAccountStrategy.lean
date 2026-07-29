/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.MertensNeymanAccount
import GameTheory.Concepts.Stochastic.MertensNeymanCriterion

/-!
# Game-facing integration of the Mertens--Neyman account controller

This file connects the account kernel to the discounted zero-sum Bellman
inequality. The main bridge rewrites a fixed-discount Bellman lower bound in
the exact outer-outcome form consumed by
`expect_correctedValuePotential_drift_ge_of_accountUpdate`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MertensNeymanAccount

open Math.Probability Math.PMFProduct

/-- Joint action and successor state under a statewise mixed profile. -/
def stateActionOutcome
    {ι : Type} (G : StochasticGame ι) [Fintype ι]
    (s : G.State) (m : ∀ i, PMF (G.Act i)) :
    PMF (G.JointAct × G.State) :=
  (pmfPi m).bind fun a =>
    (G.transition s a).bind fun s' =>
      PMF.pure (a, s')

theorem expect_stateActionOutcome
    {ι : Type} {G : StochasticGame ι} [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s : G.State) (m : ∀ i, PMF (G.Act i))
    (f : G.JointAct → G.State → ℝ) :
    expect (stateActionOutcome G s m) (fun o => f o.1 o.2) =
      expect (pmfPi m) (fun a =>
        expect (G.transition s a) (fun s' => f a s')) := by
  unfold stateActionOutcome
  rw [expect_bind]
  apply congrArg (expect (pmfPi m))
  funext a
  rw [expect_bind]
  apply congrArg (expect (G.transition s a))
  funext s'
  rw [expect_pure]

/-- A discounted Bellman lower bound is equivalent to the account proof's
outer-outcome inequality: old successor value minus current value, plus
`lam` times payoff minus old successor value. -/
theorem account_bellman_ge_of_discounted_bellman_ge
    {Ω : Type*} [Finite Ω] (d : PMF Ω)
    {lam oldCurrent : ℝ} (payoff oldNext : Ω → ℝ)
    (hbellman :
      oldCurrent ≤
        lam * expect d payoff +
          (1 - lam) * expect d oldNext) :
    0 ≤ expect d oldNext - oldCurrent +
      lam * expect d (fun ω => payoff ω - oldNext ω) := by
  rw [expect_sub]
  linarith

/-- The zero-sum discounted stationary Bellman equilibrium supplies the exact
outer-outcome account Bellman premise against an arbitrary column mixed
action. -/
theorem row_account_bellman_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {lam : ℝ} {x : G.StationaryMixedProfile}
    {V : G.State → Payoff (Fin 2)}
    (hF : G.IsDiscountedStationaryBellmanEq (1 - lam) x V)
    (hzs : G.IsZeroSum) (hVzs : ∀ s, V s 1 = -V s 0)
    (s : G.State) (d : PMF (G.Act 1)) :
    0 ≤
      expect
          (stateActionOutcome G s (Function.update (x s) 1 d))
          (fun o => V o.2 0) -
        V s 0 +
      lam *
        expect
          (stateActionOutcome G s (Function.update (x s) 1 d))
          (fun o => G.stagePayoff s o.1 0 - V o.2 0) := by
  letI : Fintype (Fin 2) := inferInstance
  have hrow :=
    hF.row_discountedAuxEU_ge hzs hVzs s d
  rw [G.discountedAuxEU_eq] at hrow
  have hpay :
      expect
          (stateActionOutcome G s (Function.update (x s) 1 d))
          (fun o => G.stagePayoff s o.1 0) =
        expect (pmfPi (Function.update (x s) 1 d))
          (fun a => G.stagePayoff s a 0) := by
    simpa using
      expect_stateActionOutcome s (Function.update (x s) 1 d)
        (fun a _ => G.stagePayoff s a 0)
  have hnext :
      expect
          (stateActionOutcome G s (Function.update (x s) 1 d))
          (fun o => V o.2 0) =
        expect (pmfPi (Function.update (x s) 1 d))
          (fun a => expect (G.transition s a) (fun s' => V s' 0)) := by
    simpa using
      expect_stateActionOutcome s (Function.update (x s) 1 d)
        (fun _ s' => V s' 0)
  apply account_bellman_ge_of_discounted_bellman_ge
    (stateActionOutcome G s (Function.update (x s) 1 d))
    (fun o => G.stagePayoff s o.1 0) (fun o => V o.2 0)
  rw [hpay, hnext]
  convert hrow using 1
  all_goals ring

/-- For the row player, a controller outcome kernel whose selected action is
the row component of `x` is the state-action outcome law of `x` against the
current column mixed action. -/
theorem outcomeKernel_eq_stateActionOutcome_row
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (C : G.MemoryController 0) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t)
    (x : G.StationaryMixedProfile)
    (hselect : C.select t h m = x h.2 0) :
    C.outcomeKernel opp h m =
      stateActionOutcome G h.2
        (Function.update (x h.2) 1 (opp 1 t h)) := by
  letI : Fintype (Fin 2) := inferInstance
  letI : DecidableEq (Fin 2) := inferInstance
  unfold MemoryController.outcomeKernel stateActionOutcome stageActionDist
  have hprofile :
      (fun i =>
        (Function.update opp 0 (fun _ _ => C.select t h m)) i t h) =
        Function.update (x h.2) 1 (opp 1 t h) := by
    funext i
    fin_cases i
    · simp [hselect]
    · simp
  rw [hprofile]

/-- Fixed-memory Bellman premise for the row account controller against an
arbitrary opposing behavior profile. -/
theorem row_controller_account_bellman_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {lam : ℝ} {x : G.StationaryMixedProfile}
    {V : G.State → Payoff (Fin 2)}
    (hF : G.IsDiscountedStationaryBellmanEq (1 - lam) x V)
    (hzs : G.IsZeroSum) (hVzs : ∀ s, V s 1 = -V s 0)
    (C : G.MemoryController 0) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t)
    (hselect : C.select t h m = x h.2 0) :
    0 ≤
      expect (C.outcomeKernel opp h m) (fun o => V o.2 0) -
        V h.2 0 +
      lam * expect (C.outcomeKernel opp h m)
        (fun o => G.stagePayoff h.2 o.1 0 - V o.2 0) := by
  rw [outcomeKernel_eq_stateActionOutcome_row C opp h m x hselect]
  exact row_account_bellman_ge hF hzs hVzs h.2 (opp 1 t h)

/-- Positive corrected-potential drift at a fixed controller memory. This
combines the zero-sum discounted Bellman inequality with the nested account
coin estimate; the only analytic premise left in the statement is the
probability-weighted value-switch budget for each successor state. -/
theorem row_controller_correctedValuePotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M s ε : ℝ} {v : ℝ → G.State → Payoff (Fin 2)}
    {x : G.StationaryMixedProfile}
    (hF : G.IsDiscountedStationaryBellmanEq
      (1 - discountRate s) x (v (discountRate s)))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ z, v (discountRate s) z 1 =
      -v (discountRate s) z 0)
    (C : G.MemoryController 0) (opp : G.BehaviorProfile)
    {t : ℕ} (hmem : G.Hist t) (m : C.Mem t)
    (hselect : C.select t hmem m = x hmem.2 0)
    (hscale : IsValidScale γ s) (hMs : M ≤ s) (hs1 : 1 < s)
    (hε : 0 ≤ ε)
    (hpayLower : ∀ a, 0 ≤ G.stagePayoff hmem.2 a 0)
    (hpayUpper : ∀ a, G.stagePayoff hmem.2 a 0 ≤ 1)
    (hvalueLower : ∀ z, 0 ≤ v (discountRate s) z 0)
    (hvalueUpper : ∀ z, v (discountRate s) z 0 ≤ 1)
    (hε2 : ε ≤ 2)
    (hsecant : ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ o : G.JointAct × G.State,
      switchBudget γ M s
          (G.stagePayoff hmem.2 o.1 0 -
            v (discountRate s) o.2 0 + ε / 2)
          (fun u => v (discountRate u) o.2 0) ≤
        ε * discountRate s / 16) :
    ε * discountRate s / 8 ≤
      expect (C.outcomeKernel opp hmem m) (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff hmem.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale
              (by
                nlinarith [hpayLower o.1, hvalueUpper o.2])
              (by
                nlinarith [hpayUpper o.1, hvalueLower o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0)) -
        v (discountRate s) hmem.2 0 +
      expect (C.outcomeKernel opp hmem m) (fun o =>
        expect
          (updatePMF γ M s
            (G.stagePayoff hmem.2 o.1 0 -
              v (discountRate s) o.2 0 + ε / 2)
            hscale
            (by
              nlinarith [hpayLower o.1, hvalueUpper o.2])
            (by
              nlinarith [hpayUpper o.1, hvalueLower o.2]))
          (fun move =>
            logCorrector s -
              logCorrector (nextAccount γ s move))) := by
  let d := C.outcomeKernel opp hmem m
  let y : G.JointAct × G.State → ℝ := fun o =>
    G.stagePayoff hmem.2 o.1 0 -
      v (discountRate s) o.2 0 + ε / 2
  let W : (G.JointAct × G.State) → ℝ → ℝ := fun o u =>
    v (discountRate u) o.2 0
  have hyLower : ∀ o, -1 ≤ y o := by
    intro o
    dsimp [y]
    nlinarith [hpayLower o.1, hvalueUpper o.2]
  have hyUpper : ∀ o, y o ≤ 2 := by
    intro o
    dsimp [y]
    nlinarith [hpayUpper o.1, hvalueLower o.2]
  have hbellman :
      0 ≤ expect d (fun o => W o s) -
          v (discountRate s) hmem.2 0 +
        discountRate s * expect d (fun o => y o - ε / 2) := by
    simpa [d, W, y] using
      row_controller_account_bellman_ge
        hF hzs hVzs C opp hmem m hselect
  exact expect_correctedValuePotential_drift_ge_of_accountUpdate
    d y W hscale hMs hs1 hyLower hyUpper hε hsecant
    (by simpa [y, W] using hbudget) hbellman

end MertensNeymanAccount
end StochasticGame
end GameTheory
