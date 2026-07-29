/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.MertensNeymanAccount
import GameTheory.Concepts.Stochastic.MertensNeymanCriterion
import GameTheory.Concepts.Stochastic.AdaptiveCertificate
import GameTheory.Concepts.Stochastic.DiscountedShapleyAlgebraic
import Math.AlgebraicSelection

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

open Filter Math.Probability Math.PMFProduct Topology

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

/-- A discounted stationary family protects one player's value coordinate
when that player's selected mixed action is fixed and every other coordinate
of the mixed profile is arbitrary. This is the symmetric Bellman interface
consumed by an account controller. -/
def IsDiscountedStationarySecurityFamily
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (who : Fin 2) (x : ℝ → G.StationaryMixedProfile)
    (v : ℝ → G.State → Payoff (Fin 2)) : Prop :=
  ∀ lam, 0 < lam → lam ≤ 1 → ∀ z (m : ∀ i, PMF (G.Act i)),
    m who = x lam z who →
      v lam z who ≤
        G.discountedAuxEU (1 - lam) (v lam) z m who

/-- The maximizing coordinate of a zero-sum discounted Bellman family has
the symmetric stationary-security property. -/
theorem isDiscountedStationarySecurityFamily_zero
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0) :
    IsDiscountedStationarySecurityFamily (G := G) 0 x v := by
  intro lam hlam hlam1 z m hm
  have hrow :=
    (hF lam hlam hlam1).row_discountedAuxEU_ge
      hzs (hVzs lam) z (m 1)
  have hprofile :
      Function.update (x lam z) 1 (m 1) = m := by
    funext i
    fin_cases i <;> simp [hm]
  simpa [hprofile] using hrow

/-- The minimizing coordinate of a zero-sum discounted Bellman family has
the same stationary-security property for its own (negated) payoff. -/
theorem isDiscountedStationarySecurityFamily_one
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0) :
    IsDiscountedStationarySecurityFamily (G := G) 1 x v := by
  intro lam hlam hlam1 z m hm
  have hcol :=
    (hF lam hlam hlam1).col_discountedAuxEU_ge
      hzs (hVzs lam) z (m 0)
  have hprofile :
      Function.update (x lam z) 0 (m 0) = m := by
    funext i
    fin_cases i <;> simp [hm]
  simpa [hprofile] using hcol

/-- The symmetric stationary-security property, rewritten in the exact
successor-value/payoff-gap form used by the account update. -/
theorem account_bellman_ge_of_securityFamily
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (s : G.State)
    (m : ∀ i, PMF (G.Act i))
    (hm : m who = x lam s who) :
    0 ≤
      expect (stateActionOutcome G s m)
          (fun o => v lam o.2 who) -
        v lam s who +
      lam * expect (stateActionOutcome G s m)
        (fun o => G.stagePayoff s o.1 who - v lam o.2 who) := by
  have hsecure := hsecurity lam hlam hlam1 s m hm
  rw [G.discountedAuxEU_eq] at hsecure
  have hpay :
      expect (stateActionOutcome G s m)
          (fun o => G.stagePayoff s o.1 who) =
        expect (pmfPi m)
          (fun a => G.stagePayoff s a who) := by
    simpa using
      expect_stateActionOutcome s m
        (fun a _ => G.stagePayoff s a who)
  have hnext :
      expect (stateActionOutcome G s m)
          (fun o => v lam o.2 who) =
        expect (pmfPi m)
          (fun a =>
            expect (G.transition s a) (fun s' => v lam s' who)) := by
    simpa using
      expect_stateActionOutcome s m
        (fun _ s' => v lam s' who)
  apply account_bellman_ge_of_discounted_bellman_ge
    (stateActionOutcome G s m)
    (fun o => G.stagePayoff s o.1 who)
    (fun o => v lam o.2 who)
  rw [hpay, hnext]
  convert hsecure using 1
  all_goals ring

/-- A controller outcome kernel is the state/action outcome law obtained by
replacing the selected player's component of the opposing profile. -/
theorem outcomeKernel_eq_stateActionOutcome_selected
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} (C : G.MemoryController who)
    (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t)
    (x : G.StationaryMixedProfile)
    (hselect : C.select t h m = x h.2 who) :
    C.outcomeKernel opp h m =
      stateActionOutcome G h.2
        (Function.update (fun i => opp i t h) who (x h.2 who)) := by
  letI : Fintype (Fin 2) := inferInstance
  letI : DecidableEq (Fin 2) := inferInstance
  unfold MemoryController.outcomeKernel stateActionOutcome stageActionDist
  have hprofile :
      (fun i =>
        (Function.update opp who
          (fun _ _ => C.select t h m)) i t h) =
        Function.update (fun i => opp i t h) who (x h.2 who) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [hselect]
    · simp [hi]
  rw [hprofile]

/-- Fixed-memory account Bellman premise for either secured player against an
arbitrary opposing behavior profile. -/
theorem controller_account_bellman_ge_of_securityFamily
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lam : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t)
    (hselect : C.select t h m = x lam h.2 who) :
    0 ≤
      expect (C.outcomeKernel opp h m) (fun o => v lam o.2 who) -
        v lam h.2 who +
      lam * expect (C.outcomeKernel opp h m)
        (fun o => G.stagePayoff h.2 o.1 who - v lam o.2 who) := by
  let profile : ∀ i, PMF (G.Act i) :=
    Function.update (fun i => opp i t h) who (x lam h.2 who)
  have hprofileWho : profile who = x lam h.2 who := by
    simp [profile]
  rw [outcomeKernel_eq_stateActionOutcome_selected
    C opp h m (x lam) hselect]
  exact account_bellman_ge_of_securityFamily
    hsecurity hlam hlam1 h.2 profile hprofileWho

/-- Positive corrected-potential drift for either secured player on an
arbitrary unit payoff/value interval. The interval's lower endpoint cancels
from every account gap; only its width is used. -/
theorem controller_correctedValuePotential_drift_ge_of_securityFamily
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M s ε : ℝ}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {x : ℝ → G.StationaryMixedProfile}
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (hmem : G.Hist t) (m : C.Mem t)
    (hselect :
      C.select t hmem m =
        x (discountRate s) hmem.2 who)
    (hscale : IsValidScale γ s) (hMs : M ≤ s) (hs1 : 1 < s)
    (hrateUpper : discountRate s ≤ 1)
    (hε : 0 ≤ ε)
    (hpayLower :
      ∀ a, lower ≤ G.stagePayoff hmem.2 a who)
    (hpayUpper :
      ∀ a, G.stagePayoff hmem.2 a who ≤ lower + 1)
    (hvalueLower :
      ∀ z, lower ≤ v (discountRate s) z who)
    (hvalueUpper :
      ∀ z, v (discountRate s) z who ≤ lower + 1)
    (hε2 : ε ≤ 2)
    (hsecant : ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ o : G.JointAct × G.State,
      switchBudget γ M s
          (G.stagePayoff hmem.2 o.1 who -
            v (discountRate s) o.2 who + ε / 2)
          (fun u => v (discountRate u) o.2 who) ≤
        ε * discountRate s / 16) :
    ε * discountRate s / 8 ≤
      expect (C.outcomeKernel opp hmem m) (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff hmem.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale
              (by
                nlinarith [hpayLower o.1, hvalueUpper o.2])
              (by
                nlinarith [hpayUpper o.1, hvalueLower o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who)) -
        v (discountRate s) hmem.2 who +
      expect (C.outcomeKernel opp hmem m) (fun o =>
        expect
          (updatePMF γ M s
            (G.stagePayoff hmem.2 o.1 who -
              v (discountRate s) o.2 who + ε / 2)
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
    G.stagePayoff hmem.2 o.1 who -
      v (discountRate s) o.2 who + ε / 2
  let W : (G.JointAct × G.State) → ℝ → ℝ := fun o u =>
    v (discountRate u) o.2 who
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
          v (discountRate s) hmem.2 who +
        discountRate s * expect d (fun o => y o - ε / 2) := by
    simpa [d, W, y] using
      controller_account_bellman_ge_of_securityFamily
        hsecurity (discountRate_pos hs1) hrateUpper
        C opp hmem m hselect
  exact expect_correctedValuePotential_drift_ge_of_accountUpdate
    d y W hscale hMs hs1 hyLower hyUpper hε hsecant
    (by simpa [y, W] using hbudget) hbellman

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

/-- The row discounted value viewed as a potential on the finite reachable
memory of the account controller. -/
def rowAccountValueMemoryPotential
    {G : StochasticGame (Fin 2)}
    (γ M : ℝ) (v : ℝ → G.State → Payoff (Fin 2))
    (t : ℕ) (h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  v (discountRate (accountAtLevel γ M k)) h.2 0

/-- The real account represented by a finite reachable exponent memory. -/
def accountLevelMemoryPotential
    {G : StochasticGame (Fin 2)}
    (γ M : ℝ) (t : ℕ) (_h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  accountAtLevel γ M k

/-- Either secured player's discounted value on the finite reachable account
memory. -/
def accountValueMemoryPotential
    {G : StochasticGame (Fin 2)} (who : Fin 2)
    (γ M : ℝ) (v : ℝ → G.State → Payoff (Fin 2))
    (t : ℕ) (h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  v (discountRate (accountAtLevel γ M k)) h.2 who

/-- Either secured player's discounted value minus the logarithmic account
corrector on finite reachable memory. -/
def accountCorrectedMemoryPotential
    {G : StochasticGame (Fin 2)} (who : Fin 2)
    (γ M : ℝ) (v : ℝ → G.State → Payoff (Fin 2))
    (t : ℕ) (h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  v (discountRate (accountAtLevel γ M k)) h.2 who -
    logCorrector (accountAtLevel γ M k)

/-- The row discounted value minus the logarithmic account corrector, viewed
as a potential on the finite reachable memory of the account controller. -/
def rowAccountCorrectedMemoryPotential
    {G : StochasticGame (Fin 2)}
    (γ M : ℝ) (v : ℝ → G.State → Payoff (Fin 2))
    (t : ℕ) (h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  v (discountRate (accountAtLevel γ M k)) h.2 0 -
    logCorrector (accountAtLevel γ M k)

/-- The published payoff/account step for the concrete finite-memory
controller at a fixed memory state. Both the next real account and the switched
discounted value are transported through the mapped exponent update. -/
theorem row_accountMemoryController_payoff_step
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
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
    (-9 * ε / 16 +
          expect (C.outcomeKernel opp h k) (fun o =>
            expect (C.update t h o.1 o.2 k) (fun k' =>
              accountLevelMemoryPotential γ M
                (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
          accountLevelMemoryPotential γ M t h k -
          accountFloorIndicator k ≤
        expect (C.outcomeKernel opp h k) (fun o =>
          G.stagePayoff h.2 o.1 0) -
        expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            rowAccountValueMemoryPotential γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k'))) := by
  dsimp only
  let C := accountMemoryController γ M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let d : PMF (G.JointAct × G.State) := C.outcomeKernel opp h k
  let s := accountAtLevel γ M k
  change -9 * ε / 16 +
        expect d (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            accountLevelMemoryPotential γ M
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        accountLevelMemoryPotential γ M t h k -
        accountFloorIndicator k ≤
      expect d (fun o => G.stagePayoff h.2 o.1 0) -
      expect d (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          rowAccountValueMemoryPotential γ M v
            (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k'))
  have hMs : M ≤ s := floor_le_accountAtLevel hfloor k
  have hscale : IsValidScale γ s :=
    isValidScale_accountAtLevel hfloor k
  have hyLower : ∀ o : G.JointAct × G.State,
      -1 ≤ G.stagePayoff h.2 o.1 0 -
        v (discountRate s) o.2 0 + ε / 2 := by
    intro o
    nlinarith [hpayLower h.2 o.1,
      hvalueUpper (discountRate s) o.2]
  have hyUpper : ∀ o : G.JointAct × G.State,
      G.stagePayoff h.2 o.1 0 -
        v (discountRate s) o.2 0 + ε / 2 ≤ 2 := by
    intro o
    nlinarith [hpayUpper h.2 o.1,
      hvalueLower (discountRate s) o.2]
  have hfloorEq :
      (if s = M then (1 : ℝ) else 0) =
        accountFloorIndicator k := by
    simp [s, accountFloorIndicator,
      accountAtLevel_eq_floor_iff hfloor]
  have hpoint : ∀ o : G.JointAct × G.State,
      -9 * ε / 16 +
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move => nextAccount γ s move - s) -
          accountFloorIndicator k ≤
        G.stagePayoff h.2 o.1 0 -
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0) := by
    intro o
    rw [← hfloorEq]
    exact payoff_sub_expectedNextValue_ge
      (ε := ε) (lam := discountRate s)
      (payoff := G.stagePayoff h.2 o.1 0)
      (V := fun u => v (discountRate u) o.2 0)
      hscale hMs hε (hrateUpper s hMs)
      (hyLower o) (hyUpper o)
      (hbudget o.2 s
        (G.stagePayoff h.2 o.1 0 -
          v (discountRate s) o.2 0 + ε / 2)
        hMs hscale (hyLower o) (hyUpper o))
  have haccountUpdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            accountLevelMemoryPotential γ M
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move => nextAccount γ s move) := by
    intro o
    simpa [C, s, accountMemoryController,
      accountLevelMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale (hyLower o) (hyUpper o) (fun u => u)
  have hvalueUpdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            rowAccountValueMemoryPotential γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0) := by
    intro o
    simpa [C, s, accountMemoryController,
      rowAccountValueMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale (hyLower o) (hyUpper o)
        (fun u => v (discountRate u) o.2 0)
  simp_rw [haccountUpdate, hvalueUpdate]
  rw [show accountLevelMemoryPotential γ M t h k = s by rfl]
  have hmean := expect_mono d _ _ hpoint
  have hnextSub : ∀ o : G.JointAct × G.State,
      expect
          (updatePMF γ M s
            (G.stagePayoff h.2 o.1 0 -
              v (discountRate s) o.2 0 + ε / 2)
            hscale (hyLower o) (hyUpper o))
          (fun move => nextAccount γ s move - s) =
        expect
          (updatePMF γ M s
            (G.stagePayoff h.2 o.1 0 -
              v (discountRate s) o.2 0 + ε / 2)
            hscale (hyLower o) (hyUpper o))
          (fun move => nextAccount γ s move) - s := by
    intro o
    rw [expect_sub, expect_const]
  simp_rw [hnextSub] at hmean
  let A : G.JointAct × G.State → ℝ := fun o =>
    expect
      (updatePMF γ M s
        (G.stagePayoff h.2 o.1 0 -
          v (discountRate s) o.2 0 + ε / 2)
        hscale (hyLower o) (hyUpper o))
      (fun move => nextAccount γ s move)
  let B : G.JointAct × G.State → ℝ := fun o =>
    expect
      (updatePMF γ M s
        (G.stagePayoff h.2 o.1 0 -
          v (discountRate s) o.2 0 + ε / 2)
        hscale (hyLower o) (hyUpper o))
      (fun move =>
        v (discountRate (nextAccount γ s move)) o.2 0)
  let P : G.JointAct × G.State → ℝ := fun o =>
    G.stagePayoff h.2 o.1 0
  change -9 * ε / 16 + expect d A - s -
      accountFloorIndicator k ≤ expect d P - expect d B
  change expect d (fun o =>
      -9 * ε / 16 + (A o - s) - accountFloorIndicator k) ≤
    expect d (fun o => P o - B o) at hmean
  rw [expect_sub, expect_add, expect_const, expect_sub, expect_const,
    expect_sub] at hmean
  rw [expect_const] at hmean
  linarith

/-- The payoff/account step for either secured player on an arbitrary unit
payoff/value interval. -/
theorem accountMemoryControllerOnUnitInterval_payoff_step
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z who) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t)
    (k : Fin (t + 1)) :
    let C := accountMemoryControllerOnUnitInterval
      lower γ M ε
      (fun lam z => x lam z who)
      (fun lam z => v lam z who)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    (-9 * ε / 16 +
          expect (C.outcomeKernel opp h k) (fun o =>
            expect (C.update t h o.1 o.2 k) (fun k' =>
              accountLevelMemoryPotential γ M
                (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
          accountLevelMemoryPotential γ M t h k -
          accountFloorIndicator k ≤
        expect (C.outcomeKernel opp h k) (fun o =>
          G.stagePayoff h.2 o.1 who) -
        expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            accountValueMemoryPotential who γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k'))) := by
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower γ M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let d : PMF (G.JointAct × G.State) := C.outcomeKernel opp h k
  let s := accountAtLevel γ M k
  change -9 * ε / 16 +
        expect d (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            accountLevelMemoryPotential γ M
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        accountLevelMemoryPotential γ M t h k -
        accountFloorIndicator k ≤
      expect d (fun o => G.stagePayoff h.2 o.1 who) -
      expect d (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          accountValueMemoryPotential who γ M v
            (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k'))
  have hMs : M ≤ s := floor_le_accountAtLevel hfloor k
  have hscale : IsValidScale γ s :=
    isValidScale_accountAtLevel hfloor k
  have hyLower : ∀ o : G.JointAct × G.State,
      -1 ≤ G.stagePayoff h.2 o.1 who -
        v (discountRate s) o.2 who + ε / 2 := by
    intro o
    nlinarith [hpayLower h.2 o.1,
      hvalueUpper (discountRate s) o.2]
  have hyUpper : ∀ o : G.JointAct × G.State,
      G.stagePayoff h.2 o.1 who -
        v (discountRate s) o.2 who + ε / 2 ≤ 2 := by
    intro o
    nlinarith [hpayUpper h.2 o.1,
      hvalueLower (discountRate s) o.2]
  have hfloorEq :
      (if s = M then (1 : ℝ) else 0) =
        accountFloorIndicator k := by
    simp [s, accountFloorIndicator,
      accountAtLevel_eq_floor_iff hfloor]
  have hpoint : ∀ o : G.JointAct × G.State,
      -9 * ε / 16 +
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move => nextAccount γ s move - s) -
          accountFloorIndicator k ≤
        G.stagePayoff h.2 o.1 who -
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who) := by
    intro o
    rw [← hfloorEq]
    exact payoff_sub_expectedNextValue_ge
      (ε := ε) (lam := discountRate s)
      (payoff := G.stagePayoff h.2 o.1 who)
      (V := fun u => v (discountRate u) o.2 who)
      hscale hMs hε (hrateUpper s hMs)
      (hyLower o) (hyUpper o)
      (hbudget o.2 s
        (G.stagePayoff h.2 o.1 who -
          v (discountRate s) o.2 who + ε / 2)
        hMs hscale (hyLower o) (hyUpper o))
  have haccountUpdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            accountLevelMemoryPotential γ M
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move => nextAccount γ s move) := by
    intro o
    simpa [C, s, accountMemoryControllerOnUnitInterval,
      accountLevelMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale (hyLower o) (hyUpper o) (fun u => u)
  have hvalueUpdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            accountValueMemoryPotential who γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who) := by
    intro o
    simpa [C, s, accountMemoryControllerOnUnitInterval,
      accountValueMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale (hyLower o) (hyUpper o)
        (fun u => v (discountRate u) o.2 who)
  simp_rw [haccountUpdate, hvalueUpdate]
  rw [show accountLevelMemoryPotential γ M t h k = s by rfl]
  have hmean := expect_mono d _ _ hpoint
  have hnextSub : ∀ o : G.JointAct × G.State,
      expect
          (updatePMF γ M s
            (G.stagePayoff h.2 o.1 who -
              v (discountRate s) o.2 who + ε / 2)
            hscale (hyLower o) (hyUpper o))
          (fun move => nextAccount γ s move - s) =
        expect
          (updatePMF γ M s
            (G.stagePayoff h.2 o.1 who -
              v (discountRate s) o.2 who + ε / 2)
            hscale (hyLower o) (hyUpper o))
          (fun move => nextAccount γ s move) - s := by
    intro o
    rw [expect_sub, expect_const]
  simp_rw [hnextSub] at hmean
  let A : G.JointAct × G.State → ℝ := fun o =>
    expect
      (updatePMF γ M s
        (G.stagePayoff h.2 o.1 who -
          v (discountRate s) o.2 who + ε / 2)
        hscale (hyLower o) (hyUpper o))
      (fun move => nextAccount γ s move)
  let B : G.JointAct × G.State → ℝ := fun o =>
    expect
      (updatePMF γ M s
        (G.stagePayoff h.2 o.1 who -
          v (discountRate s) o.2 who + ε / 2)
        hscale (hyLower o) (hyUpper o))
      (fun move =>
        v (discountRate (nextAccount γ s move)) o.2 who)
  let P : G.JointAct × G.State → ℝ := fun o =>
    G.stagePayoff h.2 o.1 who
  change -9 * ε / 16 + expect d A - s -
      accountFloorIndicator k ≤ expect d P - expect d B
  change expect d (fun o =>
      -9 * ε / 16 + (A o - s) - accountFloorIndicator k) ≤
    expect d (fun o => P o - B o) at hmean
  rw [expect_sub, expect_add, expect_const, expect_sub, expect_const,
    expect_sub] at hmean
  rw [expect_const] at hmean
  linarith

/-- Averaging the fixed-memory payoff/account step under the controller belief
gives the exact historywise inequality for the induced behavioral strategy. -/
theorem row_accountMemoryController_history_payoff_step
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
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
    let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k => accountLevelMemoryPotential γ M n hmem k
    let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k => rowAccountValueMemoryPotential γ M v n hmem k
    let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun _ _ k => accountFloorIndicator
        (show Fin (_ + 1) from k)
    (-9 * ε / 16 +
          G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential A) h -
          C.beliefPotential A t h -
          C.beliefPotential F t h ≤
        G.stageEUAt
            (Function.update opp 0 C.behaviorStrategy) h 0 -
          G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential V) h) := by
  dsimp only
  let C := accountMemoryController γ M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k => accountLevelMemoryPotential γ M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k => rowAccountValueMemoryPotential γ M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k => accountFloorIndicator
      (show Fin (n + 1) from k)
  change -9 * ε / 16 +
        G.historyContinuationEU
          (Function.update opp 0 C.behaviorStrategy)
          (C.beliefPotential A) h -
        C.beliefPotential A t h -
        C.beliefPotential F t h ≤
      G.stageEUAt
          (Function.update opp 0 C.behaviorStrategy) h 0 -
        G.historyContinuationEU
          (Function.update opp 0 C.behaviorStrategy)
          (C.beliefPotential V) h
  have hfixed : ∀ k : C.Mem t,
      -9 * ε / 16 +
            expect (C.outcomeKernel opp h k) (fun o =>
              expect (C.update t h o.1 o.2 k) (fun k' =>
                A (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
            A t h k - F t h k ≤
          expect (C.outcomeKernel opp h k) (fun o =>
            G.stagePayoff h.2 o.1 0) -
          expect (C.outcomeKernel opp h k) (fun o =>
            expect (C.update t h o.1 o.2 k) (fun k' =>
              V (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) := by
    intro k
    simpa [C, A, V, F] using
      row_accountMemoryController_payoff_step
        hfloor hε hε2 hpayLower hpayUpper
        hvalueLower hvalueUpper hrateUpper hbudget opp h k
  letI : Fintype (C.Mem t) := C.finiteMem t
  have hmean := expect_mono (C.belief t h) _ _ hfixed
  have hA :=
    C.historyContinuationEU_beliefPotential opp A h
  have hV :=
    C.historyContinuationEU_beliefPotential opp V h
  have hstage := C.stageEUAt_behaviorStrategy opp h
  unfold MemoryController.beliefPotential at hmean hA hV ⊢
  simp only [expect_sub, expect_add, expect_const] at hmean
  rw [hA, hV, hstage]
  exact hmean

/-- Posterior averaging of the symmetric payoff/account step gives the
historywise inequality for the induced behavioral strategy. -/
theorem accountMemoryControllerOnUnitInterval_history_payoff_step
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z who) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    let C := accountMemoryControllerOnUnitInterval
      lower γ M ε
      (fun lam z => x lam z who)
      (fun lam z => v lam z who)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k => accountLevelMemoryPotential γ M n hmem k
    let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k =>
        accountValueMemoryPotential who γ M v n hmem k
    let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun _ _ k => accountFloorIndicator
        (show Fin (_ + 1) from k)
    (-9 * ε / 16 +
          G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential A) h -
          C.beliefPotential A t h -
          C.beliefPotential F t h ≤
        G.stageEUAt
            (Function.update opp who C.behaviorStrategy) h who -
          G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential V) h) := by
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower γ M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k => accountLevelMemoryPotential γ M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountValueMemoryPotential who γ M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k => accountFloorIndicator
      (show Fin (n + 1) from k)
  change -9 * ε / 16 +
        G.historyContinuationEU
          (Function.update opp who C.behaviorStrategy)
          (C.beliefPotential A) h -
        C.beliefPotential A t h -
        C.beliefPotential F t h ≤
      G.stageEUAt
          (Function.update opp who C.behaviorStrategy) h who -
        G.historyContinuationEU
          (Function.update opp who C.behaviorStrategy)
          (C.beliefPotential V) h
  have hfixed : ∀ k : C.Mem t,
      -9 * ε / 16 +
            expect (C.outcomeKernel opp h k) (fun o =>
              expect (C.update t h o.1 o.2 k) (fun k' =>
                A (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
            A t h k - F t h k ≤
          expect (C.outcomeKernel opp h k) (fun o =>
            G.stagePayoff h.2 o.1 who) -
          expect (C.outcomeKernel opp h k) (fun o =>
            expect (C.update t h o.1 o.2 k) (fun k' =>
              V (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) := by
    intro k
    simpa [C, A, V, F] using
      accountMemoryControllerOnUnitInterval_payoff_step
        hfloor hε hε2 hpayLower hpayUpper
        hvalueLower hvalueUpper hrateUpper hbudget opp h k
  letI : Fintype (C.Mem t) := C.finiteMem t
  have hmean := expect_mono (C.belief t h) _ _ hfixed
  have hA :=
    C.historyContinuationEU_beliefPotential opp A h
  have hV :=
    C.historyContinuationEU_beliefPotential opp V h
  have hstage := C.stageEUAt_behaviorStrategy opp h
  unfold MemoryController.beliefPotential at hmean hA hV ⊢
  simp only [expect_sub, expect_add, expect_const] at hmean
  rw [hA, hV, hstage]
  exact hmean

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

/-- The symmetric fixed-memory corrected drift for the account controller on
an arbitrary unit payoff/value interval. -/
theorem accountMemoryControllerOnUnitInterval_correctedPotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hsecant : ∀ s, M ≤ s → ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z who) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t)
    (k : Fin (t + 1)) :
    let C := accountMemoryControllerOnUnitInterval
      lower γ M ε
      (fun lam z => x lam z who)
      (fun lam z => v lam z who)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    ε * discountRate (accountAtLevel γ M k) / 8 ≤
      expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            accountCorrectedMemoryPotential who γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        accountCorrectedMemoryPotential who γ M v t h k := by
  dsimp only
  let s := accountAtLevel γ M k
  let C := accountMemoryControllerOnUnitInterval
    lower γ M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let d : PMF (G.JointAct × G.State) :=
    C.outcomeKernel opp h k
  change ε * discountRate (accountAtLevel γ M k) / 8 ≤
    expect d (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          accountCorrectedMemoryPotential who γ M v
            (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
      accountCorrectedMemoryPotential who γ M v t h k
  have hMs : M ≤ s := floor_le_accountAtLevel hfloor k
  have hscale : IsValidScale γ s :=
    isValidScale_accountAtLevel hfloor k
  have hs1 : 1 < s := hM1.trans_le hMs
  have hbase :=
    controller_correctedValuePotential_drift_ge_of_securityFamily
      hsecurity C opp h k (by rfl) hscale hMs hs1
      (hrateUpper s hMs) hε
      (hpayLower h.2) (hpayUpper h.2)
      (hvalueLower (discountRate s))
      (hvalueUpper (discountRate s)) hε2
      (hsecant s hMs)
      (by
        intro o
        apply hbudget o.2 s
          (G.stagePayoff h.2 o.1 who -
            v (discountRate s) o.2 who + ε / 2)
          hMs hscale
        · nlinarith [hpayLower h.2 o.1,
            hvalueUpper (discountRate s) o.2]
        · nlinarith [hpayUpper h.2 o.1,
            hvalueLower (discountRate s) o.2])
  have hupdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            accountCorrectedMemoryPotential who γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who -
                logCorrector (nextAccount γ s move)) := by
    intro o
    simpa [C, s, accountMemoryControllerOnUnitInterval,
      accountCorrectedMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale
        (by
          nlinarith [hpayLower h.2 o.1,
            hvalueUpper (discountRate s) o.2])
        (by
          nlinarith [hpayUpper h.2 o.1,
            hvalueLower (discountRate s) o.2])
        (fun u =>
          v (discountRate u) o.2 who - logCorrector u)
  rw [show accountAtLevel γ M k = s by rfl]
  rw [show
    accountCorrectedMemoryPotential who γ M v t h k =
      v (discountRate s) h.2 who - logCorrector s by
        rfl]
  simp_rw [hupdate]
  calc
    ε * discountRate s / 8 ≤
        expect d (fun o =>
            expect
              (updatePMF γ M s
                (G.stagePayoff h.2 o.1 who -
                  v (discountRate s) o.2 who + ε / 2)
                hscale
                (by
                  nlinarith [hpayLower h.2 o.1,
                    hvalueUpper (discountRate s) o.2])
                (by
                  nlinarith [hpayUpper h.2 o.1,
                    hvalueLower (discountRate s) o.2]))
              (fun move =>
                v (discountRate (nextAccount γ s move)) o.2 who)) -
          v (discountRate s) h.2 who +
        expect d (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
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
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who -
                logCorrector (nextAccount γ s move))) -
          (v (discountRate s) h.2 who - logCorrector s) := by
      simp_rw [expect_sub, expect_const]
      ring

/-- Posterior averaging lifts the symmetric fixed-memory account drift to the
behavioral history law. -/
theorem accountMemoryControllerOnUnitInterval_beliefPotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hsecant : ∀ s, M ≤ s → ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z who) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    let C := accountMemoryControllerOnUnitInterval
      lower γ M ε
      (fun lam z => x lam z who)
      (fun lam z => v lam z who)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k =>
        accountCorrectedMemoryPotential who γ M v n hmem k
    ε / 8 *
        expect (C.belief t h) (fun k =>
          discountRate (accountAtLevel γ M
            ((show Fin (t + 1) from k) : ℕ))) ≤
      G.historyContinuationEU
          (Function.update opp who C.behaviorStrategy)
          (C.beliefPotential φ) h -
        C.beliefPotential φ t h := by
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower γ M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountCorrectedMemoryPotential who γ M v n hmem k
  let r : C.Mem t → ℝ := fun k =>
    ε / 8 * discountRate (accountAtLevel γ M
      ((show Fin (t + 1) from k) : ℕ))
  change ε / 8 *
      expect (C.belief t h) (fun k =>
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ))) ≤
    G.historyContinuationEU
        (Function.update opp who C.behaviorStrategy)
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
      accountMemoryControllerOnUnitInterval_correctedPotential_drift_ge
        hfloor hM1 hε hε2 hpayLower hpayUpper
        hvalueLower hvalueUpper hsecurity hrateUpper hsecant hbudget
        opp h k
  have hlift :=
    C.beliefPotential_drift_ge opp φ h r hstep
  simpa [r, expect_const_mul] using hlift

/-- The translated corrected account potential is bounded below by the lower
endpoint minus the floor corrector. -/
theorem accountCorrectedMemoryPotential_lower
    {G : StochasticGame (Fin 2)}
    {who : Fin 2} {lower γ M ε : ℝ}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hcorrector : logCorrector M ≤ ε / 8)
    (hvalueLower : ∀ lam z, lower ≤ v lam z who)
    {t : ℕ} (h : G.Hist t) (k : Fin (t + 1)) :
    lower - ε / 8 ≤
      accountCorrectedMemoryPotential who γ M v t h k := by
  have hMs : M ≤ accountAtLevel γ M k :=
    floor_le_accountAtLevel hfloor k
  have hlog :
      logCorrector (accountAtLevel γ M k) ≤ logCorrector M :=
    logCorrector_le_of_le hM1 hMs
  unfold accountCorrectedMemoryPotential
  nlinarith [hvalueLower
    (discountRate (accountAtLevel γ M k)) h.2]

/-- The translated corrected account potential is bounded above by the upper
endpoint of its unit interval. -/
theorem accountCorrectedMemoryPotential_upper
    {G : StochasticGame (Fin 2)}
    {who : Fin 2} {lower γ M : ℝ}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hvalueUpper : ∀ lam z, v lam z who ≤ lower + 1)
    {t : ℕ} (h : G.Hist t) (k : Fin (t + 1)) :
    accountCorrectedMemoryPotential who γ M v t h k ≤
      lower + 1 := by
  have hMs : M ≤ accountAtLevel γ M k :=
    floor_le_accountAtLevel hfloor k
  have hs1 : 1 < accountAtLevel γ M k := hM1.trans_le hMs
  have hlog := (logCorrector_pos hs1).le
  unfold accountCorrectedMemoryPotential
  nlinarith [hvalueUpper
    (discountRate (accountAtLevel γ M k)) h.2]

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

/-- A posterior potential in any translated unit interval, with account-rate
drift, controls total expected floor occupation under the actual history law.
The controller and secured player are abstract. -/
theorem sum_expected_belief_floorOccupation_le_on_interval
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {γ M ε : ℝ}
    (lower : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (C : G.MemoryController who)
    (level : ∀ t, C.Mem t → Fin (t + 1))
    (φ : (t : ℕ) → G.Hist t → C.Mem t → ℝ)
    (hpotentialLower : ∀ t (h : G.Hist t),
      lower - ε / 8 ≤ C.beliefPotential φ t h)
    (hpotentialUpper : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ lower + 1)
    (opp : G.BehaviorProfile) (s₀ : G.State)
    (hdrift : ∀ t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun m =>
            discountRate (accountAtLevel γ M (level t m))) ≤
        G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h)
    (T : ℕ) :
    ∑ t ∈ Finset.range T,
        G.expectedHistoryValue
          (Function.update opp who C.behaviorStrategy) s₀
          (C.beliefPotential (fun n _ m =>
            accountFloorIndicator (level n m))) t ≤
      9 / (ε * discountRate M) := by
  let σ : G.BehaviorProfile :=
    Function.update opp who C.behaviorStrategy
  let rateMemory : (t : ℕ) → G.Hist t → C.Mem t → ℝ :=
    fun t _ m => discountRate (accountAtLevel γ M (level t m))
  let floorMemory : (t : ℕ) → G.Hist t → C.Mem t → ℝ :=
    fun t _ m => accountFloorIndicator (level t m)
  let rate : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential rateMemory) t
  let potential : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t
  let floorLoss : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential floorMemory) t
  have hfloorHistory : ∀ t (h : G.Hist t),
      discountRate M *
          C.beliefPotential floorMemory t h ≤
        C.beliefPotential rateMemory t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    rw [← expect_const_mul]
    exact expect_mono _ _ _ fun m =>
      discountRate_mul_accountFloorIndicator_le
        hfloor hM1 (level t m)
  have hfloorRate : ∀ t,
      discountRate M * floorLoss t ≤ rate t := by
    intro t
    unfold floorLoss rate expectedHistoryValue
    rw [← expect_const_mul]
    exact expect_mono _ _ _ (hfloorHistory t)
  have hdriftExpected : ∀ t,
      ε * rate t / 8 ≤ potential (t + 1) - potential t := by
    intro t
    have hpoint : ∀ n (h : G.Hist n),
        ε / 8 * C.beliefPotential rateMemory n h ≤
          G.historyContinuationEU σ (C.beliefPotential φ) h -
            C.beliefPotential φ n h := by
      intro n h
      simpa [σ, rateMemory,
        MemoryController.beliefPotential] using hdrift n h
    have hmean :=
      G.expectedHistoryValue_drift_ge σ s₀
        (fun n h => ε / 8 *
          C.beliefPotential rateMemory n h)
        (C.beliefPotential φ) hpoint t
    unfold rate potential
    unfold expectedHistoryValue at hmean ⊢
    rw [expect_const_mul] at hmean
    nlinarith
  have hpotential0 : lower - ε / 8 ≤ potential 0 := by
    unfold potential expectedHistoryValue
    calc
      lower - ε / 8 =
          expect (G.histDist σ s₀ 0)
            (fun _ => lower - ε / 8) := by
            rw [expect_const]
      _ ≤ expect (G.histDist σ s₀ 0)
          (C.beliefPotential φ 0) :=
        expect_mono _ _ _ (hpotentialLower 0)
  have hpotentialT : potential T ≤ lower + 1 := by
    unfold potential expectedHistoryValue
    calc
      expect (G.histDist σ s₀ T)
          (C.beliefPotential φ T) ≤
          expect (G.histDist σ s₀ T) (fun _ => lower + 1) :=
        expect_mono _ _ _ (hpotentialUpper T)
      _ = lower + 1 := expect_const _ _
  have hsum :=
    sum_floorLoss_le_of_potential_drift_on_interval
      hε hε1 (discountRate_pos hM1) lower
      rate potential floorLoss hfloorRate hdriftExpected
      hpotential0 hpotentialT
  simpa [σ, floorLoss, floorMemory] using hsum

/-- Zero-based row specialization of
`sum_expected_belief_floorOccupation_le_on_interval`. -/
theorem sum_expected_belief_floorOccupation_le
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (C : G.MemoryController 0)
    (level : ∀ t, C.Mem t → Fin (t + 1))
    (φ : (t : ℕ) → G.Hist t → C.Mem t → ℝ)
    (hpotentialLower : ∀ t (h : G.Hist t),
      -ε / 8 ≤ C.beliefPotential φ t h)
    (hpotentialUpper : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ 1)
    (opp : G.BehaviorProfile) (s₀ : G.State)
    (hdrift : ∀ t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun m =>
            discountRate (accountAtLevel γ M (level t m))) ≤
        G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h)
    (T : ℕ) :
    ∑ t ∈ Finset.range T,
        G.expectedHistoryValue
          (Function.update opp 0 C.behaviorStrategy) s₀
          (C.beliefPotential (fun n _ m =>
            accountFloorIndicator (level n m))) t ≤
      9 / (ε * discountRate M) := by
  simpa using
    sum_expected_belief_floorOccupation_le_on_interval
      0 hε hε1 hfloor hM1 C level φ
      (fun t h => by
        have hbound := hpotentialLower t h
        linarith)
      (fun t h => by simpa using hpotentialUpper t h)
      opp s₀ hdrift T

/-- A finite-state Puiseux derivative envelope and a symmetric stationary
security family produce the complete bounded-drift, payoff-step, and
floor-occupation account package for either player on any unit interval. -/
theorem exists_accountControllerOnUnitInterval_bounded_beliefPotential_drift_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (Sextra : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z) :
    ∃ M : ℝ,
      ∃ hfloor : IsValidScale (1 + ε / 9) M,
      let C := accountMemoryControllerOnUnitInterval
        lower (1 + ε / 9) M ε
        (fun lam z => x lam z who)
        (fun lam z => v lam z who)
        hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
        (by linarith)
      let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          accountCorrectedMemoryPotential
            who (1 + ε / 9) M v n hmem k
      let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          accountLevelMemoryPotential (1 + ε / 9) M n hmem k
      let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          accountValueMemoryPotential
            who (1 + ε / 9) M v n hmem k
      let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n _ k =>
          accountFloorIndicator (show Fin (n + 1) from k)
      Sextra ≤ M ∧
      Real.exp 1 ≤ M ∧
      1 < M ∧
      logCorrector M ≤ ε / 8 ∧
      (∀ t (h : G.Hist t),
        lower - ε / 8 ≤ C.beliefPotential φ t h) ∧
      (∀ t (h : G.Hist t),
        C.beliefPotential φ t h ≤ lower + 1) ∧
      (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
        ε / 8 *
            expect (C.belief t h) (fun k =>
              discountRate (accountAtLevel (1 + ε / 9) M
                ((show Fin (t + 1) from k) : ℕ))) ≤
          G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential φ) h -
            C.beliefPotential φ t h) ∧
      (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
        -9 * ε / 16 +
              G.historyContinuationEU
                (Function.update opp who C.behaviorStrategy)
                (C.beliefPotential A) h -
              C.beliefPotential A t h -
              C.beliefPotential F t h ≤
            G.stageEUAt
                (Function.update opp who C.behaviorStrategy) h who -
              G.historyContinuationEU
                (Function.update opp who C.behaviorStrategy)
                (C.beliefPotential V) h) ∧
      (∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
        ∑ t ∈ Finset.range T,
            G.expectedHistoryValue
              (Function.update opp who C.behaviorStrategy) s₀
              (C.beliefPotential F) t ≤
          9 / (ε * discountRate M)) := by
  obtain ⟨M, hSM, hfloor, hexpM, hM1, hcorrector,
      hsecant, hbudget⟩ :=
    exists_commonAccountFloor_above_of_puiseux_deriv_bound
      Sextra hε hε1 hεquarter hβ hlam0 hderiv hbound
  refine ⟨M, hfloor, ?_⟩
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower (1 + ε / 9) M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountCorrectedMemoryPotential
        who (1 + ε / 9) M v n hmem k
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountLevelMemoryPotential (1 + ε / 9) M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountValueMemoryPotential who (1 + ε / 9) M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k =>
      accountFloorIndicator (show Fin (n + 1) from k)
  change Sextra ≤ M ∧
    Real.exp 1 ≤ M ∧
    1 < M ∧
    logCorrector M ≤ ε / 8 ∧
    (∀ t (h : G.Hist t),
      lower - ε / 8 ≤ C.beliefPotential φ t h) ∧
    (∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ lower + 1) ∧
    (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
        G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h) ∧
    (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp who C.behaviorStrategy) h who -
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential V) h) ∧
    (∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
      ∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update opp who C.behaviorStrategy) s₀
            (C.beliefPotential F) t ≤
        9 / (ε * discountRate M))
  have hpotentialLower : ∀ t (h : G.Hist t),
      lower - ε / 8 ≤ C.beliefPotential φ t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      lower - ε / 8 =
          expect (C.belief t h) (fun _ => lower - ε / 8) := by
            rw [expect_const]
      _ ≤ expect (C.belief t h) (φ t h) := by
        apply expect_mono
        intro k
        simpa [C, φ] using
          accountCorrectedMemoryPotential_lower
            hfloor hM1 hcorrector hvalueLower h k
  have hpotentialUpper : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ lower + 1 := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      expect (C.belief t h) (φ t h) ≤
          expect (C.belief t h) (fun _ => lower + 1) := by
        apply expect_mono
        intro k
        simpa [C, φ] using
          accountCorrectedMemoryPotential_upper
            hfloor hM1 hvalueUpper h k
      _ = lower + 1 := expect_const _ _
  have hdrift : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
        G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    intro opp t h
    simpa [C, φ] using
      accountMemoryControllerOnUnitInterval_beliefPotential_drift_ge
        hfloor hM1 hε.le (by linarith)
        hpayLower hpayUpper hvalueLower hvalueUpper
        hsecurity
        (fun s hs =>
          discountRate_le_one_of_exp_one_le
            (hexpM.trans hs))
        hsecant
        (fun z s y hs hscale hyLower hyUpper =>
          hbudget z s hs M y hscale hyLower hyUpper)
        opp h
  have hpayoffStep : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp who C.behaviorStrategy) h who -
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential V) h := by
    intro opp t h
    simpa [C, A, V, F] using
      accountMemoryControllerOnUnitInterval_history_payoff_step
        hfloor hε.le (by linarith)
        hpayLower hpayUpper hvalueLower hvalueUpper
        (fun s hs =>
          discountRate_le_one_of_exp_one_le
            (hexpM.trans hs))
        (fun z s y hs hscale hyLower hyUpper =>
          hbudget z s hs M y hscale hyLower hyUpper)
        opp h
  refine ⟨hSM, hexpM, hM1, hcorrector, hpotentialLower,
    hpotentialUpper, hdrift, hpayoffStep, ?_⟩
  intro opp s₀ T
  simpa [C, φ, F] using
    sum_expected_belief_floorOccupation_le_on_interval
      lower hε hε1 hfloor hM1 C
      (fun t k => show Fin (t + 1) from k)
      φ hpotentialLower hpotentialUpper opp s₀ (hdrift opp) T

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
    (Sextra : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
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
      let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          accountLevelMemoryPotential (1 + ε / 9) M n hmem k
      let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          rowAccountValueMemoryPotential (1 + ε / 9) M v n hmem k
      let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n _ k =>
          accountFloorIndicator (show Fin (n + 1) from k)
      Sextra ≤ M ∧
      Real.exp 1 ≤ M ∧
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
            C.beliefPotential φ t h) ∧
      (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
        -9 * ε / 16 +
              G.historyContinuationEU
                (Function.update opp 0 C.behaviorStrategy)
                (C.beliefPotential A) h -
              C.beliefPotential A t h -
              C.beliefPotential F t h ≤
            G.stageEUAt
                (Function.update opp 0 C.behaviorStrategy) h 0 -
              G.historyContinuationEU
                (Function.update opp 0 C.behaviorStrategy)
                (C.beliefPotential V) h) ∧
      (∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
        ∑ t ∈ Finset.range T,
            G.expectedHistoryValue
              (Function.update opp 0 C.behaviorStrategy) s₀
              (C.beliefPotential F) t ≤
          9 / (ε * discountRate M)) := by
  obtain ⟨M, hSM, hfloor, hexpM, hM1, hcorrector, hsecant, hbudget⟩ :=
    exists_commonAccountFloor_above_of_puiseux_deriv_bound
      Sextra hε hε1 hεquarter hβ hlam0 hderiv hbound
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
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountLevelMemoryPotential (1 + ε / 9) M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountValueMemoryPotential (1 + ε / 9) M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k =>
      accountFloorIndicator (show Fin (n + 1) from k)
  change Sextra ≤ M ∧
    Real.exp 1 ≤ M ∧
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
          C.beliefPotential φ t h) ∧
    (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp 0 C.behaviorStrategy) h 0 -
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential V) h) ∧
    (∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
      ∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update opp 0 C.behaviorStrategy) s₀
            (C.beliefPotential F) t ≤
        9 / (ε * discountRate M))
  have hpotentialLower : ∀ t (h : G.Hist t),
      -ε / 8 ≤ C.beliefPotential φ t h := by
    intro t h
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
  have hpotentialUpper : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ 1 := by
    intro t h
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
  have hdrift : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
        G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    intro opp t h
    simpa [C, φ] using
      row_accountMemoryController_beliefPotential_drift_ge
        hfloor hM1 hε.le (by linarith)
        hpayLower hpayUpper hvalueLower hvalueUpper
        (fun s hs =>
          hF (discountRate s)
            (discountRate_pos (hM1.trans_le hs))
            (discountRate_le_one_of_exp_one_le
              (hexpM.trans hs)))
        hzs (fun s => hVzs (discountRate s))
        hsecant
        (fun z s y hs hscale hyLower hyUpper =>
          hbudget z s hs M y hscale hyLower hyUpper)
        opp h
  have hpayoffStep : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp 0 C.behaviorStrategy) h 0 -
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential V) h := by
    intro opp t h
    simpa [C, A, V, F] using
      row_accountMemoryController_history_payoff_step
        hfloor hε.le (by linarith)
        hpayLower hpayUpper hvalueLower hvalueUpper
        (fun s hs =>
          discountRate_le_one_of_exp_one_le
            (hexpM.trans (hs)))
        (fun z s y hs hscale hyLower hyUpper =>
          hbudget z s hs M y hscale hyLower hyUpper)
        opp h
  refine ⟨hSM, hexpM, hM1, hcorrector, hpotentialLower,
    hpotentialUpper, hdrift, hpayoffStep, ?_⟩
  intro opp s₀ T
  simpa [C, φ, F] using
    sum_expected_belief_floorOccupation_le
      hε hε1 hfloor hM1 C
      (fun t k => show Fin (t + 1) from k)
      φ hpotentialLower hpotentialUpper opp s₀ (hdrift opp) T

/-- Conditional fixed-precision payoff guarantee for either secured player on
an arbitrary unit interval. -/
theorem exists_accountControllerOnUnitInterval_finiteAveragePayoff_ge_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (Starget : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ z s, Starget ≤ s →
      target z - ε / 8 ≤
        v (discountRate s) z who - logCorrector s) :
    ∃ M : ℝ,
      ∃ hfloor : IsValidScale (1 + ε / 9) M,
      Real.exp 1 ≤ M ∧
      let C := accountMemoryControllerOnUnitInterval
        lower (1 + ε / 9) M ε
        (fun lam z => x lam z who)
        (fun lam z => v lam z who)
        hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
        (by linarith)
      ∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
        0 < T →
        72 ≤ (T : ℝ) * ε ^ 2 * discountRate M →
        target s₀ - ε ≤
          G.finiteAveragePayoff s₀ T
            (Function.update opp who C.behaviorStrategy) who := by
  obtain ⟨M, hfloor, hSM, hexpM, hM1, _hcorrector,
      _hpotentialLower, _hpotentialUpper, hdrift,
      hpayoffStep, hfloorSum⟩ :=
    exists_accountControllerOnUnitInterval_bounded_beliefPotential_drift_of_puiseux
      Starget hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hsecurity hβ hlam0 hderiv hbound
  refine ⟨M, hfloor, hexpM, ?_⟩
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower (1 + ε / 9) M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountCorrectedMemoryPotential
        who (1 + ε / 9) M v n hmem k
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountLevelMemoryPotential (1 + ε / 9) M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountValueMemoryPotential who (1 + ε / 9) M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k =>
      accountFloorIndicator (show Fin (n + 1) from k)
  have hdrift' : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
          G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    exact hdrift
  have hpayoffStep' : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp who C.behaviorStrategy) h who -
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential V) h := by
    exact hpayoffStep
  have hfloorSum' : ∀ (opp : G.BehaviorProfile)
      (s₀ : G.State) (T : ℕ),
      ∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update opp who C.behaviorStrategy) s₀
            (C.beliefPotential F) t ≤
        9 / (ε * discountRate M) := by
    exact hfloorSum
  intro opp s₀ T hT hhorizon
  let σ : G.BehaviorProfile :=
    Function.update opp who C.behaviorStrategy
  let payoff : ℕ → ℝ := fun t =>
    G.expectedStagePayoff σ s₀ t who
  let nextValue : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential V) (t + 1)
  let account : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential A) t
  let floorLoss : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential F) t
  have hstep : ∀ t,
      -9 * ε / 16 + (account (t + 1) - account t) -
          floorLoss t ≤ payoff t - nextValue t := by
    intro t
    simpa [σ, payoff, nextValue, account, floorLoss] using
      G.expectedHistoryValue_payoff_step σ s₀ who
        (-9 * ε / 16)
        (C.beliefPotential A) (C.beliefPotential F)
        (C.beliefPotential V) (hpayoffStep' opp) t
  have haccountLower : ∀ t (h : G.Hist t),
      M ≤ C.beliefPotential A t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      M = expect (C.belief t h) (fun _ => M) := by
        rw [expect_const]
      _ ≤ expect (C.belief t h) (A t h) := by
        apply expect_mono
        intro k
        simpa [C, A, accountLevelMemoryPotential] using
          floor_le_accountAtLevel hfloor
            (show Fin (t + 1) from k)
  have haccount0 : account 0 = M := by
    unfold account expectedHistoryValue MemoryController.beliefPotential
    rw [G.histDist_zero, expect_pure]
    simp [C, A, MemoryController.belief,
      accountMemoryControllerOnUnitInterval,
      accountLevelMemoryPotential]
  have haccountT : M ≤ account T := by
    unfold account expectedHistoryValue
    calc
      M = expect (G.histDist σ s₀ T) (fun _ => M) := by
        rw [expect_const]
      _ ≤ expect (G.histDist σ s₀ T)
          (C.beliefPotential A T) :=
        expect_mono _ _ _ (haccountLower T)
  have hcorrectedDriftNonneg : ∀ t (h : G.Hist t),
      0 ≤
        G.historyContinuationEU σ (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    have hrate :
        0 ≤ expect (C.belief t h) (fun k =>
          discountRate (accountAtLevel (1 + ε / 9) M
            ((show Fin (t + 1) from k) : ℕ))) := by
      apply expect_nonneg
      intro k
      have hMk : M ≤ accountAtLevel (1 + ε / 9) M
          (show Fin (t + 1) from k) :=
        floor_le_accountAtLevel hfloor _
      exact (discountRate_pos (hM1.trans_le hMk)).le
    have hd := hdrift' opp t h
    dsimp [σ]
    nlinarith
  have hcorrectedMono : ∀ t,
      G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t ≤
        G.expectedHistoryValue σ s₀
          (C.beliefPotential φ) (t + 1) := by
    intro t
    have hmean :=
      G.expectedHistoryValue_drift_ge σ s₀
        (fun _ _ => 0) (C.beliefPotential φ)
        (fun n h => hcorrectedDriftNonneg n h) t
    simpa [expectedHistoryValue] using hmean
  have hcorrectedMonotone :
      Monotone (fun t =>
        G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t) :=
    monotone_nat_of_le_succ hcorrectedMono
  have hcorrected_le_value : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ C.beliefPotential V t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    apply expect_mono
    intro k
    have hMk : M ≤ accountAtLevel (1 + ε / 9) M
        (show Fin (t + 1) from k) :=
      floor_le_accountAtLevel hfloor _
    have hlog := (logCorrector_pos (hM1.trans_le hMk)).le
    simp [C, φ, V, accountCorrectedMemoryPotential,
      accountValueMemoryPotential]
    linarith
  have hinitialCorrected :
      target s₀ - ε / 8 ≤
        G.expectedHistoryValue σ s₀
          (C.beliefPotential φ) 0 := by
    unfold expectedHistoryValue MemoryController.beliefPotential
    rw [G.histDist_zero, expect_pure]
    simp [C, φ, MemoryController.belief,
      accountMemoryControllerOnUnitInterval,
      accountCorrectedMemoryPotential]
    simpa [emptyHist] using htarget s₀ M hSM
  have hnextValueLower : ∀ t,
      target s₀ - ε / 8 ≤ nextValue t := by
    intro t
    have hmono := hcorrectedMonotone (Nat.zero_le (t + 1))
    have hvalue :
        G.expectedHistoryValue σ s₀ (C.beliefPotential φ) (t + 1) ≤
          G.expectedHistoryValue σ s₀ (C.beliefPotential V) (t + 1) := by
      unfold expectedHistoryValue
      exact expect_mono _ _ _ (hcorrected_le_value (t + 1))
    unfold nextValue
    exact hinitialCorrected.trans (hmono.trans hvalue)
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hvalueAverage :
      target s₀ - ε / 8 ≤
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, nextValue t := by
    have hsum :
        ∑ _t ∈ Finset.range T, (target s₀ - ε / 8) ≤
          ∑ t ∈ Finset.range T, nextValue t :=
      Finset.sum_le_sum fun t _ => hnextValueLower t
    have hscaled :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
    have hconst :
        (T : ℝ)⁻¹ *
            (∑ _t ∈ Finset.range T, (target s₀ - ε / 8)) =
          target s₀ - ε / 8 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hTreal]
    rw [← hconst]
    exact hscaled
  have hfloorBound := hfloorSum' opp s₀ T
  have hfloorAverage :
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, floorLoss t ≤ ε / 8 := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hfloorBound
        (inv_nonneg.mpr hTreal.le)
    have hrateM : 0 < discountRate M := discountRate_pos hM1
    change (T : ℝ)⁻¹ *
        (∑ t ∈ Finset.range T,
          G.expectedHistoryValue σ s₀
            (C.beliefPotential F) t) ≤ ε / 8
    calc
      (T : ℝ)⁻¹ *
          (∑ t ∈ Finset.range T,
            G.expectedHistoryValue σ s₀
              (C.beliefPotential F) t) ≤
          (T : ℝ)⁻¹ * (9 / (ε * discountRate M)) := hscaled
      _ = 9 / ((T : ℝ) * ε * discountRate M) := by
        field_simp
      _ ≤ ε / 8 := by
        rw [div_le_div_iff₀
          (mul_pos (mul_pos hTreal hε) hrateM) (by norm_num)]
        nlinarith [sq_nonneg ε]
  have hresult :=
    average_payoff_ge_target_sub_epsilon_of_account_bounds
      hε.le payoff nextValue account floorLoss hstep hT
      (by rw [haccount0]; exact haccountT)
      hvalueAverage hfloorAverage
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simpa [payoff, σ] using hresult

/-- Conditional fixed-precision one-sided payoff guarantee. A Puiseux
derivative envelope and a tail lower bound for the initial corrected value
produce one behavioral strategy that secures the target against every opponent
at every horizon satisfying the explicit occupation threshold. -/
theorem exists_rowAccountController_finiteAveragePayoff_ge_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (Starget : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ z s, Starget ≤ s →
      target z - ε / 8 ≤
        v (discountRate s) z 0 - logCorrector s) :
    ∃ M : ℝ,
      ∃ hfloor : IsValidScale (1 + ε / 9) M,
      Real.exp 1 ≤ M ∧
      let C := accountMemoryController (1 + ε / 9) M ε
        (fun lam z => x lam z 0)
        (fun lam z => v lam z 0)
        hfloor
        hpayLower hpayUpper hvalueLower hvalueUpper hε.le
        (by linarith)
      ∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
        0 < T →
        72 ≤ (T : ℝ) * ε ^ 2 * discountRate M →
        target s₀ - ε ≤
          G.finiteAveragePayoff s₀ T
            (Function.update opp 0 C.behaviorStrategy) 0 := by
  obtain ⟨M, hfloor, hSM, hexpM, hM1, hcorrector,
      hpotentialLower, hpotentialUpper, hdrift,
      hpayoffStep, hfloorSum⟩ :=
    exists_rowAccountController_bounded_beliefPotential_drift_of_puiseux
      Starget hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hF hzs hVzs hβ hlam0 hderiv hbound
  refine ⟨M, hfloor, hexpM, ?_⟩
  dsimp only
  let C := accountMemoryController (1 + ε / 9) M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountCorrectedMemoryPotential (1 + ε / 9) M v n hmem k
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountLevelMemoryPotential (1 + ε / 9) M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountValueMemoryPotential (1 + ε / 9) M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k =>
      accountFloorIndicator (show Fin (n + 1) from k)
  have hpotentialLower' : ∀ t (h : G.Hist t),
      -ε / 8 ≤ C.beliefPotential φ t h := by
    simpa [C, φ] using hpotentialLower
  have hpotentialUpper' : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ 1 := by
    simpa [C, φ] using hpotentialUpper
  have hdrift' : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
          G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    exact hdrift
  have hpayoffStep' : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp 0 C.behaviorStrategy) h 0 -
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential V) h := by
    exact hpayoffStep
  have hfloorSum' : ∀ (opp : G.BehaviorProfile)
      (s₀ : G.State) (T : ℕ),
      ∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update opp 0 C.behaviorStrategy) s₀
            (C.beliefPotential F) t ≤
        9 / (ε * discountRate M) := by
    exact hfloorSum
  intro opp s₀ T hT hhorizon
  let σ : G.BehaviorProfile :=
    Function.update opp 0 C.behaviorStrategy
  let payoff : ℕ → ℝ := fun t =>
    G.expectedStagePayoff σ s₀ t 0
  let nextValue : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential V) (t + 1)
  let account : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential A) t
  let floorLoss : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential F) t
  have hstep : ∀ t,
      -9 * ε / 16 + (account (t + 1) - account t) -
          floorLoss t ≤ payoff t - nextValue t := by
    intro t
    simpa [σ, payoff, nextValue, account, floorLoss] using
      G.expectedHistoryValue_payoff_step σ s₀ 0
        (-9 * ε / 16)
        (C.beliefPotential A) (C.beliefPotential F)
        (C.beliefPotential V) (hpayoffStep' opp) t
  have haccountLower : ∀ t (h : G.Hist t),
      M ≤ C.beliefPotential A t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      M = expect (C.belief t h) (fun _ => M) := by
        rw [expect_const]
      _ ≤ expect (C.belief t h) (A t h) := by
        apply expect_mono
        intro k
        simpa [C, A, accountLevelMemoryPotential] using
          floor_le_accountAtLevel hfloor
            (show Fin (t + 1) from k)
  have haccount0 : account 0 = M := by
    unfold account expectedHistoryValue MemoryController.beliefPotential
    rw [G.histDist_zero, expect_pure]
    simp [C, A, MemoryController.belief,
      accountMemoryController, accountLevelMemoryPotential]
  have haccountT : M ≤ account T := by
    unfold account expectedHistoryValue
    calc
      M = expect (G.histDist σ s₀ T) (fun _ => M) := by
        rw [expect_const]
      _ ≤ expect (G.histDist σ s₀ T)
          (C.beliefPotential A T) :=
        expect_mono _ _ _ (haccountLower T)
  have hcorrectedDriftNonneg : ∀ t (h : G.Hist t),
      0 ≤
        G.historyContinuationEU σ (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    have hrate :
        0 ≤ expect (C.belief t h) (fun k =>
          discountRate (accountAtLevel (1 + ε / 9) M
            ((show Fin (t + 1) from k) : ℕ))) := by
      apply expect_nonneg
      intro k
      have hMk : M ≤ accountAtLevel (1 + ε / 9) M
          (show Fin (t + 1) from k) :=
        floor_le_accountAtLevel hfloor _
      exact (discountRate_pos (hM1.trans_le hMk)).le
    have hd := hdrift' opp t h
    dsimp [σ]
    nlinarith
  have hcorrectedMono : ∀ t,
      G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t ≤
        G.expectedHistoryValue σ s₀
          (C.beliefPotential φ) (t + 1) := by
    intro t
    have hmean :=
      G.expectedHistoryValue_drift_ge σ s₀
        (fun _ _ => 0) (C.beliefPotential φ)
        (fun n h => hcorrectedDriftNonneg n h) t
    simpa [expectedHistoryValue] using hmean
  have hcorrectedMonotone :
      Monotone (fun t =>
        G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t) :=
    monotone_nat_of_le_succ hcorrectedMono
  have hcorrected_le_value : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ C.beliefPotential V t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    apply expect_mono
    intro k
    have hMk : M ≤ accountAtLevel (1 + ε / 9) M
        (show Fin (t + 1) from k) :=
      floor_le_accountAtLevel hfloor _
    have hlog := (logCorrector_pos (hM1.trans_le hMk)).le
    simp [C, φ, V, rowAccountCorrectedMemoryPotential,
      rowAccountValueMemoryPotential]
    linarith
  have hinitialCorrected :
      target s₀ - ε / 8 ≤
        G.expectedHistoryValue σ s₀
          (C.beliefPotential φ) 0 := by
    unfold expectedHistoryValue MemoryController.beliefPotential
    rw [G.histDist_zero, expect_pure]
    simp [C, φ, MemoryController.belief,
      accountMemoryController, rowAccountCorrectedMemoryPotential]
    simpa [emptyHist] using htarget s₀ M hSM
  have hnextValueLower : ∀ t,
      target s₀ - ε / 8 ≤ nextValue t := by
    intro t
    have hmono := hcorrectedMonotone (Nat.zero_le (t + 1))
    have hvalue :
        G.expectedHistoryValue σ s₀ (C.beliefPotential φ) (t + 1) ≤
          G.expectedHistoryValue σ s₀ (C.beliefPotential V) (t + 1) := by
      unfold expectedHistoryValue
      exact expect_mono _ _ _ (hcorrected_le_value (t + 1))
    unfold nextValue
    exact hinitialCorrected.trans (hmono.trans hvalue)
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hvalueAverage :
      target s₀ - ε / 8 ≤
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, nextValue t := by
    have hsum :
        ∑ _t ∈ Finset.range T, (target s₀ - ε / 8) ≤
          ∑ t ∈ Finset.range T, nextValue t :=
      Finset.sum_le_sum fun t _ => hnextValueLower t
    have hscaled :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
    have hconst :
        (T : ℝ)⁻¹ *
            (∑ _t ∈ Finset.range T, (target s₀ - ε / 8)) =
          target s₀ - ε / 8 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hTreal]
    rw [← hconst]
    exact hscaled
  have hfloorBound := hfloorSum' opp s₀ T
  have hfloorAverage :
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, floorLoss t ≤ ε / 8 := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hfloorBound
        (inv_nonneg.mpr hTreal.le)
    have hrateM : 0 < discountRate M := discountRate_pos hM1
    change (T : ℝ)⁻¹ *
        (∑ t ∈ Finset.range T,
          G.expectedHistoryValue σ s₀
            (C.beliefPotential F) t) ≤ ε / 8
    calc
      (T : ℝ)⁻¹ *
          (∑ t ∈ Finset.range T,
            G.expectedHistoryValue σ s₀
              (C.beliefPotential F) t) ≤
          (T : ℝ)⁻¹ * (9 / (ε * discountRate M)) := hscaled
      _ = 9 / ((T : ℝ) * ε * discountRate M) := by
        field_simp
      _ ≤ ε / 8 := by
        rw [div_le_div_iff₀
          (mul_pos (mul_pos hTreal hε) hrateM) (by norm_num)]
        nlinarith [sq_nonneg ε]
  have hresult :=
    average_payoff_ge_target_sub_epsilon_of_account_bounds
      hε.le payoff nextValue account floorLoss hstep hT
      (by rw [haccount0]; exact haccountT)
      hvalueAverage hfloorAverage
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simpa [payoff, σ] using hresult

/-- Certificate-facing symmetric account theorem at one fixed precision. -/
theorem account_isOneSidedGuaranteeCertificateAt_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (Starget : ℝ) (s₀ : G.State)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ z s, Starget ≤ s →
      target z - ε / 8 ≤
        v (discountRate s) z who - logCorrector s) :
    G.IsOneSidedGuaranteeCertificateAt
      s₀ who (target s₀) ε := by
  obtain ⟨M, hfloor, hexpM, hsecure⟩ :=
    exists_accountControllerOnUnitInterval_finiteAveragePayoff_ge_of_puiseux
      target Starget hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hsecurity hβ hlam0 hderiv hbound htarget
  let C := accountMemoryControllerOnUnitInterval
    lower (1 + ε / 9) M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  have hrateM : 0 < discountRate M :=
    discountRate_pos
      ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hexpM)
  have hcoef : 0 < ε ^ 2 * discountRate M :=
    mul_pos (sq_pos_of_pos hε) hrateM
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (72 / (ε ^ 2 * discountRate M))
  let T₀ := max 2 (N + 1)
  refine ⟨C.behaviorStrategy, T₀, le_max_left _ _, ?_⟩
  intro opp T hT
  have hNsucc : N + 1 ≤ T :=
    (le_max_right 2 (N + 1)).trans hT
  have hTpos : 0 < T :=
    lt_of_lt_of_le (by norm_num) ((le_max_left 2 (N + 1)).trans hT)
  have hNT : (N : ℝ) < (T : ℝ) := by
    exact_mod_cast (show N < T by omega)
  have hquot : 72 / (ε ^ 2 * discountRate M) < (T : ℝ) :=
    hN.trans hNT
  have hhorizonStrict :
      72 < (T : ℝ) * (ε ^ 2 * discountRate M) :=
    (div_lt_iff₀ hcoef).mp hquot
  have hhorizon :
      72 ≤ (T : ℝ) * ε ^ 2 * discountRate M := by
    nlinarith
  simpa [C] using hsecure opp s₀ T hTpos hhorizon

/-- Certificate-facing form of the conditional account theorem at one fixed
precision. The securing controller and horizon threshold are chosen before the
opponent profile. -/
theorem rowAccount_isOneSidedGuaranteeCertificateAt_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (Starget : ℝ) (s₀ : G.State)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ z s, Starget ≤ s →
      target z - ε / 8 ≤
        v (discountRate s) z 0 - logCorrector s) :
    G.IsOneSidedGuaranteeCertificateAt s₀ 0 (target s₀) ε := by
  obtain ⟨M, hfloor, hexpM, hsecure⟩ :=
    exists_rowAccountController_finiteAveragePayoff_ge_of_puiseux
      target Starget hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hF hzs hVzs hβ hlam0 hderiv hbound htarget
  let C := accountMemoryController (1 + ε / 9) M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  have hrateM : 0 < discountRate M :=
    discountRate_pos
      ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hexpM)
  have hcoef : 0 < ε ^ 2 * discountRate M :=
    mul_pos (sq_pos_of_pos hε) hrateM
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (72 / (ε ^ 2 * discountRate M))
  let T₀ := max 2 (N + 1)
  refine ⟨C.behaviorStrategy, T₀, le_max_left _ _, ?_⟩
  intro opp T hT
  have hNsucc : N + 1 ≤ T :=
    (le_max_right 2 (N + 1)).trans hT
  have hTpos : 0 < T :=
    lt_of_lt_of_le (by norm_num) ((le_max_left 2 (N + 1)).trans hT)
  have hNT : (N : ℝ) < (T : ℝ) := by
    exact_mod_cast (show N < T by omega)
  have hquot : 72 / (ε ^ 2 * discountRate M) < (T : ℝ) :=
    hN.trans hNT
  have hhorizonStrict :
      72 < (T : ℝ) * (ε ^ 2 * discountRate M) :=
    (div_lt_iff₀ hcoef).mp hquot
  have hhorizon :
      72 ≤ (T : ℝ) * ε ^ 2 * discountRate M := by
    nlinarith
  simpa [C] using hsecure opp s₀ T hTpos hhorizon

/-- Right-convergence of either player's discounted value coordinate gives the
corrected-value tail required by the account construction, uniformly over the
finite state space. -/
theorem exists_tail_correctedValue_lower_of_tendsto_for
    {G : StochasticGame (Fin 2)}
    [Finite G.State] {who : Fin 2}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (target : G.State → ℝ)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z who)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z)))
    {η : ℝ} (hη : 0 < η) :
    ∃ S : ℝ, ∀ z s, S ≤ s →
      target z - η / 8 ≤
        v (discountRate s) z who - logCorrector s := by
  have hrate :
      Tendsto discountRate atTop
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_discountRate_atTop, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
    exact discountRate_pos hs
  have hvalue : ∀ z,
      ∀ᶠ s : ℝ in atTop,
        target z - η / 16 <
          v (discountRate s) z who := by
    intro z
    exact (tendsto_order.1 ((hlimit z).comp hrate)).1
      (target z - η / 16) (by linarith)
  have hvalues :
      ∀ᶠ s : ℝ in atTop, ∀ z,
        target z - η / 16 <
          v (discountRate s) z who := by
    rw [Filter.eventually_all]
    exact hvalue
  have hcorrector :
      ∀ᶠ s : ℝ in atTop, logCorrector s < η / 16 :=
    (tendsto_order.1 tendsto_logCorrector_atTop).2
      (η / 16) (by linarith)
  have htail :
      ∀ᶠ s : ℝ in atTop, ∀ z,
        target z - η / 8 ≤
          v (discountRate s) z who - logCorrector s := by
    filter_upwards [hvalues, hcorrector] with s hs hlog
    intro z
    have hz := hs z
    linarith
  rcases eventually_atTop.1 htail with ⟨S, hS⟩
  exact ⟨S, fun z s hs => hS s hs z⟩

/-- Convergence of the discounted values from positive discount rates gives
the corrected-value tail required by the account construction. Finiteness of
the state space makes the convergence threshold uniform in the state. -/
theorem exists_tail_correctedValue_lower_of_tendsto
    {G : StochasticGame (Fin 2)}
    [Finite G.State]
    {v : ℝ → G.State → Payoff (Fin 2)}
    (target : G.State → ℝ)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z)))
    {η : ℝ} (hη : 0 < η) :
    ∃ S : ℝ, ∀ z s, S ≤ s →
      target z - η / 8 ≤
        v (discountRate s) z 0 - logCorrector s := by
  have hrate :
      Tendsto discountRate atTop
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_discountRate_atTop, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
    exact discountRate_pos hs
  have hvalue : ∀ z,
      ∀ᶠ s : ℝ in atTop,
        target z - η / 16 <
          v (discountRate s) z 0 := by
    intro z
    exact (tendsto_order.1 ((hlimit z).comp hrate)).1
      (target z - η / 16) (by linarith)
  have hvalues :
      ∀ᶠ s : ℝ in atTop, ∀ z,
        target z - η / 16 <
          v (discountRate s) z 0 := by
    rw [Filter.eventually_all]
    exact hvalue
  have hcorrector :
      ∀ᶠ s : ℝ in atTop, logCorrector s < η / 16 :=
    (tendsto_order.1 tendsto_logCorrector_atTop).2
      (η / 16) (by linarith)
  have htail :
      ∀ᶠ s : ℝ in atTop, ∀ z,
        target z - η / 8 ≤
          v (discountRate s) z 0 - logCorrector s := by
    filter_upwards [hvalues, hcorrector] with s hs hlog
    intro z
    have hz := hs z
    linarith
  rcases eventually_atTop.1 htail with ⟨S, hS⟩
  exact ⟨S, fun z s hs => hS s hs z⟩

/-- Full conditional one-sided securing certificate for either player on an
arbitrary unit payoff/value interval. -/
theorem account_isOneSidedGuaranteeCertificate_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ η : ℝ, 0 < η → ∃ S : ℝ, ∀ z s, S ≤ s →
      target z - η / 8 ≤
        v (discountRate s) z who - logCorrector s) :
    G.IsOneSidedGuaranteeCertificate s₀ who (target s₀) := by
  intro δ hδ
  let ε := min (δ / 2) (1 / 8)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (half_pos hδ) (by norm_num)
  have hε1 : ε ≤ 1 := by
    calc
      ε ≤ 1 / 8 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hεquarter : ε < 1 / 4 := by
    calc
      ε ≤ 1 / 8 := min_le_right _ _
      _ < 1 / 4 := by norm_num
  have hεδ : ε ≤ δ := by
    calc
      ε ≤ δ / 2 := min_le_left _ _
      _ ≤ δ := by linarith
  obtain ⟨S, hS⟩ := htarget ε hε
  obtain ⟨σwho, T₀, hT₀, hsecure⟩ :=
    account_isOneSidedGuaranteeCertificateAt_of_puiseux
      target S s₀ hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hsecurity hβ hlam0 hderiv hbound hS
  refine ⟨σwho, T₀, hT₀, ?_⟩
  intro opp T hT
  have hbase := hsecure opp T hT
  linarith

/-- Symmetric one-sided account certificate from a Puiseux derivative
envelope and right-convergence of the secured discounted-value coordinate. -/
theorem account_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z who)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsOneSidedGuaranteeCertificate s₀ who (target s₀) := by
  apply account_isOneSidedGuaranteeCertificate_of_puiseux
    target s₀ hpayLower hpayUpper hvalueLower hvalueUpper
    hsecurity hβ hlam0 hderiv hbound
  intro η hη
  exact exists_tail_correctedValue_lower_of_tendsto_for
    target hlimit hη

/-- The column account certificate in the natural zero-sum normalization:
player one's own payoff and value lie in `[-1,0]`. -/
theorem colAccount_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, -1 ≤ G.stagePayoff z a 1)
    (hpayUpper : ∀ z a, G.stagePayoff z a 1 ≤ 0)
    (hvalueLower : ∀ lam z, -1 ≤ v lam z 1)
    (hvalueUpper : ∀ lam z, v lam z 1 ≤ 0)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 1) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsOneSidedGuaranteeCertificate s₀ 1 (target s₀) := by
  apply account_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
    (who := (1 : Fin 2)) (lower := (-1 : ℝ))
    target s₀ hpayLower
    (fun z a => by simpa using hpayUpper z a)
    hvalueLower
    (fun lam z => by simpa using hvalueUpper lam z)
    (isDiscountedStationarySecurityFamily_one hF hzs hVzs)
    hβ hlam0 hderiv hbound hlimit

/-- A player-zero one-sided certificate is a mechanism-neutral row tracking
certificate. -/
theorem isRowTrackingCertificate_of_oneSidedGuarantee
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {s₀ : G.State} {w : ℝ}
    (h : G.IsOneSidedGuaranteeCertificate s₀ 0 w) :
    G.IsRowTrackingCertificate w s₀ := by
  intro ε hε
  obtain ⟨σ, T₀, _hT₀, hsecure⟩ := h ε hε
  refine ⟨σ, T₀, ?_⟩
  intro dev T hT
  simpa using hsecure (G.pairBehaviorProfile σ dev) T hT

/-- A player-one one-sided certificate at value `-w` is the
mechanism-neutral column securing certificate. -/
theorem securesCol_of_oneSidedGuarantee
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {s₀ : G.State} {w : ℝ}
    (h : G.IsOneSidedGuaranteeCertificate s₀ 1 (-w)) :
    G.SecuresCol w s₀ := by
  intro ε hε
  obtain ⟨σ, T₀, _hT₀, hsecure⟩ := h ε hε
  refine ⟨σ, T₀, ?_⟩
  intro dev T hT
  simpa using hsecure (G.pairBehaviorProfile dev σ) T hT

/-- Finite-index two-player counterpart of the Bool one-sided-certificate
wrapper: two security certificates assemble into a zero-sum uniform
equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_oneSidedGuarantees
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (hzs : G.IsZeroSum) (s₀ : G.State) (w : ℝ)
    (hrow : G.IsOneSidedGuaranteeCertificate s₀ 0 w)
    (hcol : G.IsOneSidedGuaranteeCertificate s₀ 1 (-w)) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then w else -w) := by
  exact G.uniformValue_of_rowColumnTrackingCertificates
    hzs w s₀
    (isRowTrackingCertificate_of_oneSidedGuarantee hrow)
    (securesCol_of_oneSidedGuarantee hcol)

/-- Full conditional one-sided securing certificate. The Puiseux envelope is
fixed for the discounted-value family, while the corrected-value tail
threshold may depend on the requested precision. -/
theorem rowAccount_isOneSidedGuaranteeCertificate_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ η : ℝ, 0 < η → ∃ S : ℝ, ∀ z s, S ≤ s →
      target z - η / 8 ≤
        v (discountRate s) z 0 - logCorrector s) :
    G.IsOneSidedGuaranteeCertificate s₀ 0 (target s₀) := by
  intro δ hδ
  let ε := min (δ / 2) (1 / 8)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (half_pos hδ) (by norm_num)
  have hε1 : ε ≤ 1 := by
    calc
      ε ≤ 1 / 8 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hεquarter : ε < 1 / 4 := by
    calc
      ε ≤ 1 / 8 := min_le_right _ _
      _ < 1 / 4 := by norm_num
  have hεδ : ε ≤ δ := by
    calc
      ε ≤ δ / 2 := min_le_left _ _
      _ ≤ δ := by linarith
  obtain ⟨S, hS⟩ := htarget ε hε
  obtain ⟨σwho, T₀, hT₀, hsecure⟩ :=
    rowAccount_isOneSidedGuaranteeCertificateAt_of_puiseux
      target S s₀ hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hF hzs hVzs hβ hlam0 hderiv hbound hS
  refine ⟨σwho, T₀, hT₀, ?_⟩
  intro opp T hT
  have hbase := hsecure opp T hT
  linarith

/-- The one-sided account certificate from the standard analytic inputs:
a Puiseux derivative envelope and convergence of the discounted values from
positive discount rates. -/
theorem rowAccount_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsOneSidedGuaranteeCertificate s₀ 0 (target s₀) := by
  apply rowAccount_isOneSidedGuaranteeCertificate_of_puiseux
    target s₀ hpayLower hpayUpper hvalueLower hvalueUpper
    hF hzs hVzs hβ hlam0 hderiv hbound
  intro η hη
  exact exists_tail_correctedValue_lower_of_tendsto
    target hlimit hη

/-- Conditional two-player zero-sum uniform-value theorem from the standard
discounted family data. The single row-coordinate Puiseux envelope and
right-limit generate both one-sided account certificates by zero-sum
antisymmetry. -/
theorem isUniformEquilibriumPayoff_of_puiseux_discountedValue_of_value_zeroSum
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then target s₀ else -target s₀) := by
  have hrow :
      G.IsOneSidedGuaranteeCertificate s₀ 0 (target s₀) :=
    rowAccount_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
      target s₀ hpayLower hpayUpper hvalueLower hvalueUpper
      hF hzs hVzs hβ hlam0 hderiv hbound hlimit
  have hpayLowerOne : ∀ z a, -1 ≤ G.stagePayoff z a 1 := by
    intro z a
    rw [hzs z a]
    nlinarith [hpayUpper z a]
  have hpayUpperOne : ∀ z a, G.stagePayoff z a 1 ≤ 0 := by
    intro z a
    rw [hzs z a]
    nlinarith [hpayLower z a]
  have hvalueLowerOne : ∀ lam z, -1 ≤ v lam z 1 := by
    intro lam z
    rw [hVzs lam z]
    nlinarith [hvalueUpper lam z]
  have hvalueUpperOne : ∀ lam z, v lam z 1 ≤ 0 := by
    intro lam z
    rw [hVzs lam z]
    nlinarith [hvalueLower lam z]
  have hderivOne : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 1) (-v' z lam) lam := by
    intro z lam hlam hlam0
    apply (hderiv z lam hlam hlam0).neg.congr_of_eventuallyEq
    filter_upwards [] with u
    exact hVzs u z
  have hboundOne : ∀ z lam, 0 < lam → lam < lam0 z →
      |-v' z lam| ≤ lam ^ (β z - 1) / lam0 z := by
    intro z lam hlam hlam0
    simpa using hbound z lam hlam hlam0
  have hlimitOne : ∀ z,
      Tendsto (fun lam => v lam z 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (-target z)) := by
    intro z
    simpa only [hVzs] using (hlimit z).neg
  have hcol :
      G.IsOneSidedGuaranteeCertificate s₀ 1 (-target s₀) := by
    simpa using
      colAccount_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
        (fun z => -target z) s₀
        hpayLowerOne hpayUpperOne
        hvalueLowerOne hvalueUpperOne
        hF hzs hVzs hβ hlam0 hderivOne hboundOne hlimitOne
  exact isUniformEquilibriumPayoff_of_oneSidedGuarantees
    hzs s₀ (target s₀) hrow hcol

/-- Conditional two-player zero-sum uniform-value theorem from a discounted
Bellman family and a Puiseux envelope for player zero.

No separate zero-sum hypothesis on the selected value family is needed.
On the natural rate domain, every zero-sum discounted Bellman equilibrium
has antisymmetric values by
`IsDiscountedStationaryBellmanEq.value_zeroSum`; outside that domain the
unused player-one coordinate is normalized to the negative of player zero. -/
theorem isUniformEquilibriumPayoff_of_puiseux_discountedValue
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then target s₀ else -target s₀) := by
  let vz : ℝ → G.State → Payoff (Fin 2) :=
    fun lam z who => if who = 0 then v lam z 0 else -v lam z 0
  have hvz_zero (lam : ℝ) (z : G.State) : vz lam z 0 = v lam z 0 := by
    simp [vz]
  have hvz_one (lam : ℝ) (z : G.State) : vz lam z 1 = -vz lam z 0 := by
    simp [vz]
  have hFz : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (vz lam) := by
    intro lam hlam hlam1
    have hEq := hF lam hlam hlam1
    have hEqzs :
        ∀ z, v lam z 1 = -v lam z 0 :=
      hEq.value_zeroSum (by linarith) (by linarith) hzs
    have hvz : vz lam = v lam := by
      funext z who
      fin_cases who
      · exact hvz_zero lam z
      · change -v lam z 0 = v lam z 1
        exact (hEqzs z).symm
    rwa [hvz]
  apply
    isUniformEquilibriumPayoff_of_puiseux_discountedValue_of_value_zeroSum
      (v := vz) target s₀ hpayLower hpayUpper
  · intro lam z
    simpa [hvz_zero] using hvalueLower lam z
  · intro lam z
    simpa [hvz_zero] using hvalueUpper lam z
  · exact hFz
  · exact hzs
  · exact hvz_one
  · exact hβ
  · exact hlam0
  · intro z lam hlam hlam0'
    simpa only [hvz_zero] using hderiv z lam hlam hlam0'
  · exact hbound
  · intro z
    simpa only [hvz_zero] using hlimit z

/-- A genuine coordinatewise Puiseux reparameterization discharges both
analytic hypotheses of the zero-sum account theorem.

For every state coordinate, `v(λ) = g(λ^q)` with `q > 0`, a regular factor
continuous at zero, and a bounded derivative of that factor supplies:

* the account derivative envelope, by
  `Math.puiseuxDerivativeEnvelope_of_rpow_reparam`;
* the right limit `g(0)`, by `Math.tendsto_zero_of_rpow_reparam`.

This theorem makes the Puiseux data and discounted Bellman family sufficient;
it does not require a separate game-facing convergence or derivative
estimate. -/
theorem isUniformEquilibriumPayoff_of_puiseux_reparam_discountedValue
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (q ρ K : G.State → ℝ)
    (g g' : G.State → ℝ → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hq : ∀ z, 0 < q z)
    (hρ : ∀ z, 0 < ρ z)
    (hK : ∀ z, 0 ≤ K z)
    (hreparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      v lam z 0 = g z (lam ^ q z))
    (hgcontinuous : ∀ z, ContinuousAt (g z) 0)
    (hgderiv : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      HasDerivAt (g z) (g' z (lam ^ q z)) (lam ^ q z))
    (hgbound : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      |g' z (lam ^ q z)| ≤ K z) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then g s₀ 0 else -g s₀ 0) := by
  have hEnvelope : ∀ z, ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt (fun u => v u z 0)
            (g' z (lam ^ q z) *
              (q z * lam ^ (q z - 1))) lam ∧
          |g' z (lam ^ q z) *
              (q z * lam ^ (q z - 1))| ≤
            lam ^ (q z - 1) / lam0 := by
    intro z
    exact Math.puiseuxDerivativeEnvelope_of_rpow_reparam
      (hq z) (hρ z) (hK z)
      (hreparam z) (hgderiv z) (hgbound z)
  choose lam0 hlam0 hEnvelope using hEnvelope
  let v' : G.State → ℝ → ℝ := fun z lam =>
    g' z (lam ^ q z) * (q z * lam ^ (q z - 1))
  have hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').1
  have hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (q z - 1) / lam0 z := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').2
  have hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (g z 0)) := by
    intro z
    exact Math.tendsto_zero_of_rpow_reparam
      (hq z) (hρ z) (hreparam z) (hgcontinuous z)
  exact isUniformEquilibriumPayoff_of_puiseux_discountedValue
    (fun z => g z 0) s₀
    hpayLower hpayUpper hvalueLower hvalueUpper
    hF hzs hq hlam0 hderiv hbound hlimit

/-- A coordinatewise algebraic branch that becomes regular after a positive
power reparameterization yields the zero-sum uniform payoff.

Unlike `isUniformEquilibriumPayoff_of_puiseux_reparam_discountedValue`, this
theorem does not ask for a derivative function or a derivative bound for the
regular factors. A polynomial relation with a simple limiting root supplies
that calculus data through
`Math.puiseuxDerivativeEnvelope_of_regular_reparam_polynomial_root`. -/
theorem isUniformEquilibriumPayoff_of_regular_reparam_algebraic_discountedValue
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (P : G.State → Polynomial (Polynomial ℝ))
    (q ρw ρg : G.State → ℝ)
    (g : G.State → ℝ → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hq : ∀ z, 0 < q z)
    (hρw : ∀ z, 0 < ρw z)
    (hρg : ∀ z, 0 < ρg z)
    (hreparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρw z) →
      v lam z 0 = g z (lam ^ q z))
    (hgcontinuousAt : ∀ z, ContinuousAt (g z) 0)
    (hgcontinuousOn : ∀ z,
      ContinuousOn (g z) (Set.Ioo 0 (ρg z)))
    (hgroot : ∀ z t, t ∈ Set.Ioo (0 : ℝ) (ρg z) →
      Math.bivEval (P z) t (g z t) = 0)
    (hgregular : ∀ z,
      Math.bivEval (Polynomial.derivative (P z)) 0 (g z 0) ≠ 0) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then g s₀ 0 else -g s₀ 0) := by
  let g' : G.State → ℝ → ℝ := fun z t =>
    -(Math.bivEval (Math.bivDerivLam (P z)) t (g z t)) /
      Math.bivEval (Polynomial.derivative (P z)) t (g z t)
  have hEnvelope : ∀ z, ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt (fun u => v u z 0)
            (g' z (lam ^ q z) *
              (q z * lam ^ (q z - 1))) lam ∧
          |g' z (lam ^ q z) *
              (q z * lam ^ (q z - 1))| ≤
            lam ^ (q z - 1) / lam0 := by
    intro z
    exact Math.puiseuxDerivativeEnvelope_of_regular_reparam_polynomial_root
      (P := P z) (w := fun lam => v lam z 0) (g := g z)
      (hq z) (hρw z) (hρg z)
      (hreparam z) (hgcontinuousAt z) (hgcontinuousOn z)
      (hgroot z) (hgregular z)
  choose lam0 hlam0 hEnvelope using hEnvelope
  let v' : G.State → ℝ → ℝ := fun z lam =>
    g' z (lam ^ q z) * (q z * lam ^ (q z - 1))
  have hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').1
  have hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (q z - 1) / lam0 z := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').2
  have hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (g z 0)) := by
    intro z
    exact Math.tendsto_zero_of_rpow_reparam
      (hq z) (hρw z) (hreparam z) (hgcontinuousAt z)
  exact isUniformEquilibriumPayoff_of_puiseux_discountedValue
    (fun z => g z 0) s₀
    hpayLower hpayUpper hvalueLower hvalueUpper
    hF hzs hq hlam0 hderiv hbound hlimit

/-- Regular algebraic discounted-value branches yield the zero-sum
uniform payoff without a Newton--Puiseux construction.

If each selected value coordinate extends continuously to `λ = 0`, remains a
root of a bivariate polynomial for positive small rates, and is a simple root
at `(0, v(0))`, then
`Math.puiseuxDerivativeEnvelope_of_regular_polynomial_root` supplies the
account envelope with exponent `1`. Continuity supplies the limit. Coordinates
singular at the limiting point do not satisfy this theorem's regularity
hypothesis. -/
theorem isUniformEquilibriumPayoff_of_regular_algebraic_discountedValue
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (P : G.State → Polynomial (Polynomial ℝ))
    (ρ : G.State → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hρ : ∀ z, 0 < ρ z)
    (hcontinuousAt : ∀ z,
      ContinuousAt (fun lam => v lam z 0) 0)
    (hcontinuousOn : ∀ z,
      ContinuousOn (fun lam => v lam z 0)
        (Set.Ioo 0 (ρ z)))
    (hroot : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      Math.bivEval (P z) lam (v lam z 0) = 0)
    (hregular : ∀ z,
      Math.bivEval (Polynomial.derivative (P z)) 0 (v 0 z 0) ≠ 0) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then v 0 s₀ 0 else -v 0 s₀ 0) := by
  let v' : G.State → ℝ → ℝ := fun z lam =>
    -(Math.bivEval (Math.bivDerivLam (P z)) lam (v lam z 0)) /
      Math.bivEval (Polynomial.derivative (P z)) lam (v lam z 0)
  have hEnvelope : ∀ z, ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt (fun u => v u z 0) (v' z lam) lam ∧
          |v' z lam| ≤ lam ^ ((1 : ℝ) - 1) / lam0 := by
    intro z
    exact Math.puiseuxDerivativeEnvelope_of_regular_polynomial_root
      (hρ z) (hcontinuousAt z) (hcontinuousOn z)
      (hroot z) (hregular z)
  choose lam0 hlam0 hEnvelope using hEnvelope
  have hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').1
  have hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ ((1 : ℝ) - 1) / lam0 z := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').2
  have hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (v 0 z 0)) := by
    intro z
    exact (hcontinuousAt z).tendsto.mono_left inf_le_left
  exact isUniformEquilibriumPayoff_of_puiseux_discountedValue
    (fun z => v 0 z 0) s₀
    hpayLower hpayUpper hvalueLower hvalueUpper
    hF hzs (fun _ => zero_lt_one) hlam0
    hderiv hbound hlimit

/-- The canonical rate-parameterized discounted Shapley payoff admits one
stationary Bellman profile at every natural rate `0 < λ ≤ 1`. The fixed-rate
profile is supplied by the Fink–Shapley identification theorem; finite choice
assembles the profiles into a total family. -/
theorem exists_discountedShapleyRateBellmanProfileFamily
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum) :
    ∃ x : ℝ → G.StationaryMixedProfile,
      ∀ lam, 0 < lam → lam ≤ 1 →
        G.IsDiscountedStationaryBellmanEq
          (1 - lam) (x lam) (G.discountedShapleyRatePayoff lam) := by
  have hpayAbs : ∀ s a who, |G.stagePayoff s a who| ≤ (1 : ℝ) := by
    intro s a who
    fin_cases who
    · change |G.stagePayoff s a 0| ≤ 1
      rw [abs_le]
      exact ⟨by linarith [hpayLower s a], hpayUpper s a⟩
    · change |G.stagePayoff s a 1| ≤ 1
      rw [hzs s a, abs_neg, abs_le]
      exact ⟨by linarith [hpayLower s a], hpayUpper s a⟩
  let x₀ : G.StationaryMixedProfile :=
    fun _ who =>
      PMF.pure (Classical.choice (inferInstance : Nonempty (G.Act who)))
  have hex (lam : ℝ) :
      ∃ x : G.StationaryMixedProfile,
        0 < lam → lam ≤ 1 →
          G.IsDiscountedStationaryBellmanEq
            (1 - lam) x (G.discountedShapleyRatePayoff lam) := by
    by_cases hlam : 0 < lam ∧ lam ≤ 1
    · obtain ⟨x, hx⟩ :=
        G.exists_isDiscountedStationaryBellmanEq_discountedShapleyValue
          (discountFactorOfRate_lt_one hlam.1)
          1 zero_le_one hpayAbs hzs
      have hvalue :
          (fun s who =>
            if who = 0 then
              G.discountedShapleyValue
                (discountFactorOfRate_lt_one hlam.1) s
            else
              -G.discountedShapleyValue
                (discountFactorOfRate_lt_one hlam.1) s) =
            G.discountedShapleyRatePayoff lam := by
        funext s who
        fin_cases who <;>
          simp [discountedShapleyRatePayoff,
            G.discountedShapleyRateValue_eq hlam.1]
      rw [coe_discountFactorOfRate hlam.2, hvalue] at hx
      exact ⟨x, fun _ _ => hx⟩
    · exact ⟨x₀, fun hlam0 hlam1 => (hlam ⟨hlam0, hlam1⟩).elim⟩
  choose x hx using hex
  exact ⟨x, hx⟩

/-- A bounded canonical discounted-value coordinate has a right limit when it
lies on a nondegenerate bivariate algebraic branch. Positive-rate continuity
and boundedness are supplied by the Shapley fixed-point theory. -/
theorem exists_discountedShapleyRateValue_limit_of_polynomial_root
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (P : G.State → Polynomial (Polynomial ℝ))
    (ρ : G.State → ℝ)
    (hρ : ∀ z, 0 < ρ z)
    (hρle : ∀ z, ρ z ≤ 1)
    (hP : ∀ z, P z ≠ 0)
    (hroot : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρ z) →
      Math.bivEval (P z) l
        (G.discountedShapleyRateValue l z) = 0)
    (hRv : ∀ z,
      Polynomial.resultant (P z)
        (Polynomial.derivative (P z)) ≠ 0)
    (hRlam : ∀ z,
      Polynomial.resultant (P z)
        (Math.bivDerivLam (P z)) ≠ 0) :
    ∃ L : G.State → ℝ, ∀ z,
      Tendsto
        (fun l => G.discountedShapleyRateValue l z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (L z)) := by
  have hexists (z : G.State) :
      ∃ L : ℝ,
        Tendsto
          (fun l => G.discountedShapleyRateValue l z)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 L) := by
    have hcontinuous :
        ContinuousOn
          (fun l => G.discountedShapleyRateValue l z)
          (Set.Ioo (0 : ℝ) (ρ z)) :=
      (G.continuousOn_discountedShapleyRateValue_apply
        hzs hpayLower hpayUpper z).mono (by
          intro l hl
          exact ⟨hl.1, hl.2.le.trans (hρle z)⟩)
    apply Math.exists_tendsto_nhdsWithin_zero_of_polynomial_root
      (hρ z) hcontinuous
      (hP z) (hroot z) (hRv z) (hRlam z)
      (C := (1 : ℝ))
    intro l _hl
    rw [abs_le]
    constructor
    · have hnonneg :=
        G.discountedShapleyRateValue_nonneg
          hzs hpayLower l z
      linarith
    · exact G.discountedShapleyRateValue_le_one
        hzs hpayLower hpayUpper l z
  choose L hL using hexists
  exact ⟨L, hL⟩

/-- Regular coordinatewise algebraic branches of the canonical discounted
Shapley value produce the zero-sum uniform payoff.

The stationary Bellman family, value bounds, and positive-rate continuity are
constructed internally. The hypotheses retain only the coordinate equations,
their right limits, and simplicity of the limiting roots. -/
theorem isUniformEquilibriumPayoff_of_regular_algebraic_discountedShapleyRateValue
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (P : G.State → Polynomial (Polynomial ℝ))
    (ρ L : G.State → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (hρ : ∀ z, 0 < ρ z)
    (hρle : ∀ z, ρ z ≤ 1)
    (hlimit : ∀ z,
      Tendsto
        (fun l => G.discountedShapleyRateValue l z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (L z)))
    (hroot : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρ z) →
      Math.bivEval (P z) l
        (G.discountedShapleyRateValue l z) = 0)
    (hregular : ∀ z,
      Math.bivEval (Polynomial.derivative (P z)) 0 (L z) ≠ 0) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then L s₀ else -L s₀) := by
  let g : G.State → ℝ → ℝ := fun z l =>
    if 0 < l then G.discountedShapleyRateValue l z else L z
  obtain ⟨x, hx⟩ :=
    exists_discountedShapleyRateBellmanProfileFamily G
      hpayLower hpayUpper hzs
  have h :=
    isUniformEquilibriumPayoff_of_regular_reparam_algebraic_discountedValue
      P (fun _ => (1 : ℝ)) ρ ρ g s₀
      hpayLower hpayUpper
      (fun l z =>
        G.discountedShapleyRateValue_nonneg hzs hpayLower l z)
      (fun l z =>
        G.discountedShapleyRateValue_le_one
          hzs hpayLower hpayUpper l z)
      hx hzs (fun _ => zero_lt_one) hρ hρ
      (by
        intro z l hl
        simp [g, hl.1])
      (by
        intro z
        rw [Metric.continuousAt_iff]
        intro ε hε
        obtain ⟨δ, hδ, hclose⟩ :=
          (Metric.tendsto_nhdsWithin_nhds.mp (hlimit z)) ε hε
        refine ⟨δ, hδ, ?_⟩
        intro l hl
        by_cases hl0 : 0 < l
        · simpa [g, hl0] using hclose hl0 hl
        · simpa [g, hl0] using hε)
      (by
        intro z
        refine ((G.continuousOn_discountedShapleyRateValue_apply
          hzs hpayLower hpayUpper z).mono ?_).congr ?_
        · intro l hl
          exact ⟨hl.1, hl.2.le.trans (hρle z)⟩
        · intro l hl
          simp [g, hl.1])
      (by
        intro z l hl
        simpa [g, hl.1] using hroot z l hl)
      (by
        intro z
        simpa [g] using hregular z)
  simpa [g] using h

/-- Nondegenerate coordinate polynomials reduce the canonical zero-sum
discounted-value problem to an explicit endpoint dichotomy: either every
limiting root is simple and the account construction yields a uniform payoff,
or a named state has a singular limiting root. -/
theorem discountedShapleyRateValue_regular_or_singular_limit
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (P : G.State → Polynomial (Polynomial ℝ))
    (ρ : G.State → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (hρ : ∀ z, 0 < ρ z)
    (hρle : ∀ z, ρ z ≤ 1)
    (hP : ∀ z, P z ≠ 0)
    (hroot : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρ z) →
      Math.bivEval (P z) l
        (G.discountedShapleyRateValue l z) = 0)
    (hRv : ∀ z,
      Polynomial.resultant (P z)
        (Polynomial.derivative (P z)) ≠ 0)
    (hRlam : ∀ z,
      Polynomial.resultant (P z)
        (Math.bivDerivLam (P z)) ≠ 0) :
    (∃ L : G.State → ℝ,
        (∀ z,
          Tendsto
            (fun l => G.discountedShapleyRateValue l z)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (L z))) ∧
        G.IsUniformEquilibriumPayoff s₀
          (fun who => if who = 0 then L s₀ else -L s₀)) ∨
      ∃ (L : G.State → ℝ) (z : G.State),
        (∀ y,
          Tendsto
            (fun l => G.discountedShapleyRateValue l y)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (L y))) ∧
        Math.bivEval
          (Polynomial.derivative (P z)) 0 (L z) = 0 := by
  obtain ⟨L, hL⟩ :=
    exists_discountedShapleyRateValue_limit_of_polynomial_root
      G hpayLower hpayUpper hzs P ρ hρ hρle hP
      hroot hRv hRlam
  by_cases hregular : ∀ z,
      Math.bivEval
        (Polynomial.derivative (P z)) 0 (L z) ≠ 0
  · left
    exact ⟨L, hL,
      isUniformEquilibriumPayoff_of_regular_algebraic_discountedShapleyRateValue
        G P ρ L s₀ hpayLower hpayUpper hzs
        hρ hρle hL hroot hregular⟩
  · right
    simp only [not_forall, not_not] at hregular
    obtain ⟨z, hz⟩ := hregular
    exact ⟨L, z, hL, hz⟩

/-- A sufficient discounted-value selection package for the two-player
zero-sum account construction.

It contains a stationary discounted Bellman family on the natural rate domain
and a coordinatewise Puiseux reparameterization of player zero's value.
The analytic account envelope and limiting payoff are deliberately absent:
they are derived from these fields by
`isUniformEquilibriumPayoff_of_puiseux_reparam_discountedValue`.

Its fields state the Bewley--Kohlberg/Newton--Puiseux selection interface used
by the verification theorem below. -/
structure PuiseuxDiscountedValueSelection
    (G : StochasticGame (Fin 2))
    [Finite G.State] [∀ i, Finite (G.Act i)] where
  x : ℝ → G.StationaryMixedProfile
  v : ℝ → G.State → Payoff (Fin 2)
  q : G.State → ℝ
  ρ : G.State → ℝ
  K : G.State → ℝ
  g : G.State → ℝ → ℝ
  g' : G.State → ℝ → ℝ
  valueLower : ∀ lam z, 0 ≤ v lam z 0
  valueUpper : ∀ lam z, v lam z 0 ≤ 1
  bellman : ∀ lam, 0 < lam → lam ≤ 1 →
    G.IsDiscountedStationaryBellmanEq
      (1 - lam) (x lam) (v lam)
  exponent_pos : ∀ z, 0 < q z
  radius_pos : ∀ z, 0 < ρ z
  derivativeBound_nonneg : ∀ z, 0 ≤ K z
  reparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
    v lam z 0 = g z (lam ^ q z)
  regular_continuousAt_zero : ∀ z, ContinuousAt (g z) 0
  regular_hasDerivAt : ∀ z lam,
    lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      HasDerivAt (g z) (g' z (lam ^ q z)) (lam ^ q z)
  regular_derivative_bound : ∀ z lam,
    lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      |g' z (lam ^ q z)| ≤ K z

/-- Construct the complete semantic selection package from a coordinatewise
Puiseux reparameterization of the canonical discounted Shapley value.

The stationary Bellman family and the `[0,1]` value bounds are derived
internally. Thus the remaining input is exactly the
Bewley–Kohlberg/Newton–Puiseux branch data for the canonical row value. -/
theorem exists_puiseuxDiscountedValueSelection_of_discountedShapleyRateValue_reparam
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (q ρ K : G.State → ℝ)
    (g g' : G.State → ℝ → ℝ)
    (hq : ∀ z, 0 < q z)
    (hρ : ∀ z, 0 < ρ z)
    (hK : ∀ z, 0 ≤ K z)
    (hreparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      G.discountedShapleyRateValue lam z = g z (lam ^ q z))
    (hgcontinuous : ∀ z, ContinuousAt (g z) 0)
    (hgderiv : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      HasDerivAt (g z) (g' z (lam ^ q z)) (lam ^ q z))
    (hgbound : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      |g' z (lam ^ q z)| ≤ K z) :
    ∃ S : PuiseuxDiscountedValueSelection G,
      S.v = G.discountedShapleyRatePayoff ∧ S.g = g := by
  obtain ⟨x, hx⟩ :=
    exists_discountedShapleyRateBellmanProfileFamily G
      hpayLower hpayUpper hzs
  refine ⟨{
    x := x
    v := G.discountedShapleyRatePayoff
    q := q
    ρ := ρ
    K := K
    g := g
    g' := g'
    valueLower := ?_
    valueUpper := ?_
    bellman := hx
    exponent_pos := hq
    radius_pos := hρ
    derivativeBound_nonneg := hK
    reparam := ?_
    regular_continuousAt_zero := hgcontinuous
    regular_hasDerivAt := hgderiv
    regular_derivative_bound := hgbound
  }, rfl, rfl⟩
  · intro lam z
    simpa using
      G.discountedShapleyRateValue_nonneg hzs hpayLower lam z
  · intro lam z
    simpa using
      G.discountedShapleyRateValue_le_one
        hzs hpayLower hpayUpper lam z
  · intro z lam hlam
    simpa using hreparam z lam hlam

/-- A `PuiseuxDiscountedValueSelection` produces the normalized zero-sum
uniform payoff. -/
theorem PuiseuxDiscountedValueSelection.isUniformEquilibriumPayoff
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (S : PuiseuxDiscountedValueSelection G)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then S.g s₀ 0 else -S.g s₀ 0) := by
  exact isUniformEquilibriumPayoff_of_puiseux_reparam_discountedValue
    S.q S.ρ S.K S.g S.g' s₀
    hpayLower hpayUpper S.valueLower S.valueUpper
    S.bellman hzs
    S.exponent_pos S.radius_pos S.derivativeBound_nonneg
    S.reparam S.regular_continuousAt_zero
    S.regular_hasDerivAt S.regular_derivative_bound

/-- A coordinatewise Puiseux reparameterization of the canonical discounted
Shapley value is sufficient for the normalized zero-sum uniform payoff.

All stationary-profile, Bellman, value-bound, and zero-sum-identification
data are constructed internally. This is the direct game-facing
Bewley–Kohlberg/Newton–Puiseux boundary. -/
theorem isUniformEquilibriumPayoff_of_discountedShapleyRateValue_reparam
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (q ρ K : G.State → ℝ)
    (g g' : G.State → ℝ → ℝ)
    (hq : ∀ z, 0 < q z)
    (hρ : ∀ z, 0 < ρ z)
    (hK : ∀ z, 0 ≤ K z)
    (hreparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      G.discountedShapleyRateValue lam z = g z (lam ^ q z))
    (hgcontinuous : ∀ z, ContinuousAt (g z) 0)
    (hgderiv : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      HasDerivAt (g z) (g' z (lam ^ q z)) (lam ^ q z))
    (hgbound : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      |g' z (lam ^ q z)| ≤ K z) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then g s₀ 0 else -g s₀ 0) := by
  obtain ⟨S, _hSv, hSg⟩ :=
    exists_puiseuxDiscountedValueSelection_of_discountedShapleyRateValue_reparam
      G hpayLower hpayUpper hzs q ρ K g g'
      hq hρ hK hreparam hgcontinuous hgderiv hgbound
  have h := S.isUniformEquilibriumPayoff
    s₀ hpayLower hpayUpper hzs
  rwa [hSg] at h

/-- Existence-facing zero-sum wrapper from a discounted-value selection
package. -/
theorem exists_uniformEquilibriumPayoff_of_puiseuxDiscountedValueSelection
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (S : PuiseuxDiscountedValueSelection G)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum) :
    ∃ u : Payoff (Fin 2), G.IsUniformEquilibriumPayoff s₀ u := by
  exact ⟨fun who =>
      if who = 0 then S.g s₀ 0 else -S.g s₀ 0,
    S.isUniformEquilibriumPayoff s₀ hpayLower hpayUpper hzs⟩

end MertensNeymanAccount
end StochasticGame
end GameTheory
