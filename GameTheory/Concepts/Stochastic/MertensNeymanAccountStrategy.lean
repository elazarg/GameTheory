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

/-- The row discounted value minus the logarithmic account corrector, viewed
as a potential on the finite reachable memory of the account controller. -/
def rowAccountCorrectedMemoryPotential
    {G : StochasticGame (Fin 2)}
    (γ M : ℝ) (v : ℝ → G.State → Payoff (Fin 2))
    (t : ℕ) (h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  v (discountRate (accountAtLevel γ M k)) h.2 0 -
    logCorrector (accountAtLevel γ M k)

/-- The fixed-memory corrected drift for the concrete account controller.
This theorem performs the change of variables from the real three-point
account coin to the finite exponent update used by `MemoryController`. -/
theorem row_accountMemoryController_correctedPotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ s, M ≤ s →
      G.IsDiscountedStationaryBellmanEq
        (1 - discountRate s) (x (discountRate s))
          (v (discountRate s)))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ s z, v (discountRate s) z 1 =
      -v (discountRate s) z 0)
    (hsecant : ∀ s, M ≤ s → ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z 0) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t)
    (k : Fin (t + 1)) :
    let C := accountMemoryController γ M ε
      (fun lam z => x lam z 0)
      (fun lam z => v lam z 0)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    ε * discountRate (accountAtLevel γ M k) / 8 ≤
      expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            rowAccountCorrectedMemoryPotential γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        rowAccountCorrectedMemoryPotential γ M v t h k := by
  dsimp only
  let s := accountAtLevel γ M k
  let C := accountMemoryController γ M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let d : PMF (G.JointAct × G.State) :=
    C.outcomeKernel opp h k
  change ε * discountRate (accountAtLevel γ M k) / 8 ≤
    expect d (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          rowAccountCorrectedMemoryPotential γ M v
            (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
      rowAccountCorrectedMemoryPotential γ M v t h k
  have hMs : M ≤ s := floor_le_accountAtLevel hfloor k
  have hscale : IsValidScale γ s :=
    isValidScale_accountAtLevel hfloor k
  have hs1 : 1 < s := hM1.trans_le hMs
  have hbase :=
    row_controller_correctedValuePotential_drift_ge
      (hF s hMs) hzs (hVzs s) C opp h k
      (by rfl) hscale hMs hs1 hε
      (hpayLower h.2) (hpayUpper h.2)
      (hvalueLower (discountRate s))
      (hvalueUpper (discountRate s)) hε2
      (hsecant s hMs)
      (by
        intro o
        apply hbudget o.2 s
          (G.stagePayoff h.2 o.1 0 -
            v (discountRate s) o.2 0 + ε / 2)
          hMs hscale
        · nlinarith [hpayLower h.2 o.1,
            hvalueUpper (discountRate s) o.2]
        · nlinarith [hpayUpper h.2 o.1,
            hvalueLower (discountRate s) o.2])
  have hupdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            rowAccountCorrectedMemoryPotential γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0 -
                logCorrector (nextAccount γ s move)) := by
    intro o
    simpa [C, s, accountMemoryController,
      rowAccountCorrectedMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale
        (by
          nlinarith [hpayLower h.2 o.1,
            hvalueUpper (discountRate s) o.2])
        (by
          nlinarith [hpayUpper h.2 o.1,
            hvalueLower (discountRate s) o.2])
        (fun u =>
          v (discountRate u) o.2 0 - logCorrector u)
  rw [show accountAtLevel γ M k = s by rfl]
  rw [show
    rowAccountCorrectedMemoryPotential γ M v t h k =
      v (discountRate s) h.2 0 - logCorrector s by
        rfl]
  simp_rw [hupdate]
  calc
    ε * discountRate s / 8 ≤
        expect d (fun o =>
            expect
              (updatePMF γ M s
                (G.stagePayoff h.2 o.1 0 -
                  v (discountRate s) o.2 0 + ε / 2)
                hscale
                (by
                  nlinarith [hpayLower h.2 o.1,
                    hvalueUpper (discountRate s) o.2])
                (by
                  nlinarith [hpayUpper h.2 o.1,
                    hvalueLower (discountRate s) o.2]))
              (fun move =>
                v (discountRate (nextAccount γ s move)) o.2 0)) -
          v (discountRate s) h.2 0 +
        expect d (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              logCorrector s -
                logCorrector (nextAccount γ s move))) := by
          simpa [d] using hbase
    _ = expect d (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0 -
                logCorrector (nextAccount γ s move))) -
          (v (discountRate s) h.2 0 - logCorrector s) := by
      simp_rw [expect_sub, expect_const]
      ring

/-- Averaging the concrete fixed-memory account estimate under the controller
posterior gives a historywise drift for the induced behavioral strategy. -/
theorem row_accountMemoryController_beliefPotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ s, M ≤ s →
      G.IsDiscountedStationaryBellmanEq
        (1 - discountRate s) (x (discountRate s))
          (v (discountRate s)))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ s z, v (discountRate s) z 1 =
      -v (discountRate s) z 0)
    (hsecant : ∀ s, M ≤ s → ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z 0) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    let C := accountMemoryController γ M ε
      (fun lam z => x lam z 0)
      (fun lam z => v lam z 0)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k =>
        rowAccountCorrectedMemoryPotential γ M v n hmem k
    ε / 8 *
        expect (C.belief t h) (fun k =>
          discountRate (accountAtLevel γ M
            ((show Fin (t + 1) from k) : ℕ))) ≤
      G.historyContinuationEU
          (Function.update opp 0 C.behaviorStrategy)
          (C.beliefPotential φ) h -
        C.beliefPotential φ t h := by
  dsimp only
  let C := accountMemoryController γ M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountCorrectedMemoryPotential γ M v n hmem k
  let r : C.Mem t → ℝ := fun k =>
    ε / 8 * discountRate (accountAtLevel γ M
      ((show Fin (t + 1) from k) : ℕ))
  change ε / 8 *
      expect (C.belief t h) (fun k =>
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ))) ≤
    G.historyContinuationEU
        (Function.update opp 0 C.behaviorStrategy)
        (C.beliefPotential φ) h -
      C.beliefPotential φ t h
  have hstep : ∀ k : C.Mem t,
      r k ≤
        expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            φ (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
          φ t h k := by
    intro k
    change ε / 8 *
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ)) ≤
      expect (C.outcomeKernel opp h k) (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          φ (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        φ t h k
    rw [show ε / 8 *
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ)) =
      ε * discountRate (accountAtLevel γ M
        ((show Fin (t + 1) from k) : ℕ)) / 8 by ring]
    simpa [C, φ] using
      row_accountMemoryController_correctedPotential_drift_ge
        hfloor hM1 hε hε2 hpayLower hpayUpper
        hvalueLower hvalueUpper hF hzs hVzs hsecant hbudget
        opp h k
  have hlift :=
    C.beliefPotential_drift_ge opp φ h r hstep
  simpa [r, expect_const_mul] using hlift

/-- The corrected account potential is bounded below once the floor makes the
logarithmic corrector at most `ε/8`. -/
theorem rowAccountCorrectedMemoryPotential_lower
    {G : StochasticGame (Fin 2)}
    {γ M ε : ℝ} {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hcorrector : logCorrector M ≤ ε / 8)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    {t : ℕ} (h : G.Hist t) (k : Fin (t + 1)) :
    -ε / 8 ≤ rowAccountCorrectedMemoryPotential γ M v t h k := by
  have hMs : M ≤ accountAtLevel γ M k :=
    floor_le_accountAtLevel hfloor k
  have hlog :
      logCorrector (accountAtLevel γ M k) ≤ logCorrector M :=
    logCorrector_le_of_le hM1 hMs
  unfold rowAccountCorrectedMemoryPotential
  nlinarith [hvalueLower
    (discountRate (accountAtLevel γ M k)) h.2]

/-- The corrected account potential is at most one under normalized discounted
values. -/
theorem rowAccountCorrectedMemoryPotential_upper
    {G : StochasticGame (Fin 2)}
    {γ M : ℝ} {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    {t : ℕ} (h : G.Hist t) (k : Fin (t + 1)) :
    rowAccountCorrectedMemoryPotential γ M v t h k ≤ 1 := by
  have hMs : M ≤ accountAtLevel γ M k :=
    floor_le_accountAtLevel hfloor k
  have hs1 : 1 < accountAtLevel γ M k := hM1.trans_le hMs
  have hlog := (logCorrector_pos hs1).le
  unfold rowAccountCorrectedMemoryPotential
  nlinarith [hvalueUpper
    (discountRate (accountAtLevel γ M k)) h.2]

/-- A finite-state Puiseux derivative envelope produces a concrete account
controller whose posterior corrected potential is uniformly bounded and has
positive historywise drift against every opposing behavior profile. This is
the conditional zero-sum account certificate immediately upstream of the
floor-occupation telescope. -/
theorem exists_rowAccountController_bounded_beliefPotential_drift_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z) :
    ∃ M : ℝ,
      ∃ hfloor : IsValidScale (1 + ε / 9) M,
      let C := accountMemoryController (1 + ε / 9) M ε
        (fun lam z => x lam z 0)
        (fun lam z => v lam z 0)
        hfloor
        hpayLower hpayUpper hvalueLower hvalueUpper hε.le
        (by linarith)
      let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          rowAccountCorrectedMemoryPotential (1 + ε / 9) M v n hmem k
      1 < M ∧
      logCorrector M ≤ ε / 8 ∧
      (∀ t (h : G.Hist t),
        -ε / 8 ≤ C.beliefPotential φ t h) ∧
      (∀ t (h : G.Hist t),
        C.beliefPotential φ t h ≤ 1) ∧
      (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
        ε / 8 *
            expect (C.belief t h) (fun k =>
              discountRate (accountAtLevel (1 + ε / 9) M
                ((show Fin (t + 1) from k) : ℕ))) ≤
          G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential φ) h -
            C.beliefPotential φ t h) := by
  obtain ⟨M, hfloor, hM1, hcorrector, hsecant, hbudget⟩ :=
    exists_commonAccountFloor_of_puiseux_deriv_bound
      hε hε1 hεquarter hβ hlam0 hderiv hbound
  refine ⟨M, hfloor, ?_⟩
  dsimp only
  let C := accountMemoryController (1 + ε / 9) M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountCorrectedMemoryPotential (1 + ε / 9) M v n hmem k
  change 1 < M ∧
    logCorrector M ≤ ε / 8 ∧
    (∀ t (h : G.Hist t),
      -ε / 8 ≤ C.beliefPotential φ t h) ∧
    (∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ 1) ∧
    (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
        G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h)
  refine ⟨hM1, hcorrector, ?_, ?_, ?_⟩
  · intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      -ε / 8 =
          expect (C.belief t h) (fun _ => -ε / 8) := by
            rw [expect_const]
      _ ≤ expect (C.belief t h) (φ t h) := by
        apply expect_mono
        intro k
        simpa [C, φ] using
          rowAccountCorrectedMemoryPotential_lower
            hfloor hM1 hcorrector hvalueLower h k
  · intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      expect (C.belief t h) (φ t h) ≤
          expect (C.belief t h) (fun _ => 1) := by
        apply expect_mono
        intro k
        simpa [C, φ] using
          rowAccountCorrectedMemoryPotential_upper
            hfloor hM1 hvalueUpper h k
      _ = 1 := expect_const _ _
  · intro opp t h
    simpa [C, φ] using
      row_accountMemoryController_beliefPotential_drift_ge
        hfloor hM1 hε.le (by linarith)
        hpayLower hpayUpper hvalueLower hvalueUpper
        (fun s hs =>
          hF (discountRate s)
            (discountRate_pos (hM1.trans_le hs)))
        hzs (fun s => hVzs (discountRate s))
        hsecant
        (fun z s y hs hscale hyLower hyUpper =>
          hbudget z s hs M y hscale hyLower hyUpper)
        opp h

end MertensNeymanAccount
end StochasticGame
end GameTheory
