import GameTheory.Zermelo
import Mathlib.Tactic.Linarith

/-!
# One-Shot Deviation Principle

For finite perfect-information extensive-form games, a pure strategy profile
is a subgame-perfect equilibrium if and only if no player has a profitable
one-shot deviation at any decision node.

## Main definitions

- `HasNoOneShotDeviation` — no player benefits from changing a single action

## Main theorems

- `spe_hasNoOneShotDeviation` — SPE implies no profitable one-shot deviation
- `hasNoOneShotDeviation_spe` — converse (for perfect-info games)
- `oneShotDeviation_iff_spe` — the equivalence (ODP)
-/

namespace EFG

open GameTheory

-- ============================================================================
-- No profitable one-shot deviation
-- ============================================================================

/-- A profile has no profitable one-shot deviation if at every reachable
    decision node, the action chosen by `σ` gives at least as much EU
    as any alternative action, with the rest of the profile unchanged. -/
def HasNoOneShotDeviation (G : EFGGame) [Fintype G.Outcome]
    (σ : PureProfile G.inf) : Prop :=
  ∀ {p : G.inf.Player} (I : G.inf.Infoset p)
    (next : G.inf.Act I → GameTree G.inf G.Outcome),
    (∃ h : List (HistoryStep G.inf), ReachBy h G.tree (.decision I next)) →
    ∀ (a' : G.inf.Act I),
      expect ((next (σ p I)).evalDist (pureToBehavioral σ))
        (fun ω => G.utility ω p) ≥
      expect ((next a').evalDist (pureToBehavioral σ))
        (fun ω => G.utility ω p)

-- ============================================================================
-- Easy direction: SPE → no profitable one-shot deviation
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- SPE implies no profitable one-shot deviation (for perfect-info games). -/
theorem spe_hasNoOneShotDeviation (G : EFGGame) [Fintype G.Outcome]
    (σ : PureProfile G.inf) (hpi : IsPerfectInfo G.tree)
    (hspe : G.IsSubgamePerfectEq σ) : HasNoOneShotDeviation G σ := by
  intro p I next ⟨h, hreach⟩ a'
  have hSub := perfectInfo_isSubgame_decision G.tree hpi I next hreach
  -- Extract Nash inequality with our local Function.update instance
  have hDecN : expect ((.decision I next : GameTree G.inf G.Outcome).evalDist
        (pureToBehavioral σ)) (fun ω => G.utility ω p) ≥
      expect ((.decision I next : GameTree G.inf G.Outcome).evalDist
        (pureToBehavioral (Function.update σ p (Function.update (σ p) I a'))))
        (fun ω => G.utility ω p) := by
    have h := hspe _ hSub p (Function.update (σ p) I a')
    simp only [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
      evalDist_decision] at h
    simp only [evalDist_decision, pureToBehavioral] at h ⊢
    rw [update_eq_update_of_decEq] at h
    exact h
  -- Simplify both sides
  have hEvalL : (.decision I next : GameTree G.inf G.Outcome).evalDist (pureToBehavioral σ) =
      (next (σ p I)).evalDist (pureToBehavioral σ) := by
    simp [evalDist_decision, pureToBehavioral]
  have hEvalR : (.decision I next : GameTree G.inf G.Outcome).evalDist
      (pureToBehavioral (Function.update σ p (Function.update (σ p) I a'))) =
      (next a').evalDist
        (pureToBehavioral (Function.update σ p (Function.update (σ p) I a'))) := by
    simp [evalDist_decision, pureToBehavioral]
  -- In subtree next a', the one-shot deviation agrees with σ
  have hpi_dec : IsPerfectInfo (.decision I next) := IsPerfectInfo_subtree hpi hreach
  have hAgree : (next a').evalDist
      (pureToBehavioral (Function.update σ p (Function.update (σ p) I a'))) =
      (next a').evalDist (pureToBehavioral σ) := by
    apply evalDist_eq_of_agree
    intro q J hIn
    by_cases hq : q = p
    · subst hq
      have hJI : J ≠ I := fun hEq =>
        perfectInfo_root_not_in_subtree (hpi := hpi_dec) (hEq ▸ hIn)
      simp [Function.update, hJI]
    · simp [Function.update, hq]
  rw [hEvalL, hEvalR, hAgree] at hDecN
  exact hDecN

-- ============================================================================
-- Hard direction: no profitable one-shot deviation → SPE
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- Key inductive lemma: if σ has no profitable one-shot deviation (globally),
    then σ is Nash at every reachable subtree of a perfect-info tree.
    Proof by structural induction on the tree. -/
theorem nash_of_noOSD (G : EFGGame) [Fintype G.Outcome]
    (σ : PureProfile G.inf)
    (hnosd : HasNoOneShotDeviation G σ) :
    ∀ (t : GameTree G.inf G.Outcome),
      IsPerfectInfo t →
      ∀ hroot, ReachBy hroot G.tree t →
      ∀ {h u}, ReachBy h t u →
        (G.withTree u).toStrategicKernelGame.IsNashFor
          (KernelGame.euPref G.toStrategicKernelGame) σ := by
  intro t hpi
  induction t with
  | terminal z =>
    intro hroot hreach_root h u hr
    cases hr
    exact terminal_isNashFor_euPref z σ
  | chance k μ hk next ih =>
    intro hroot hreach_root h u hr
    have hpi_next : ∀ b : Fin k, IsPerfectInfo (next b) :=
      fun b => IsPerfectInfo_subtree (root := .chance k μ hk next) hpi
        (.chance b (.here _))
    cases hr with
    | here =>
      intro who s'
      have hNnext : ∀ b : Fin k,
          (G.withTree (next b)).toStrategicKernelGame.IsNashFor
            (KernelGame.euPref G.toStrategicKernelGame) σ :=
        fun b => ih b (hpi_next b) _ (ReachBy_append hreach_root (.chance b (.here _)))
          (.here _)
      have hpoint : ∀ b : Fin k,
          expect ((next b).evalDist (pureToBehavioral σ)) (fun ω => G.utility ω who) ≥
          expect ((next b).evalDist
            (pureToBehavioral (@Function.update G.inf.Player
              (fun p => PureStrategy G.inf p)
              (fun a b => Classical.propDecidable (a = b)) σ who s')))
            (fun ω => G.utility ω who) := by
        intro b
        have hb := hNnext b who s'
        simpa [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree] using hb
      simpa [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
        evalDist_chance, expect_bind,
        update_eq_update_of_decEq (instDecidableEqFin G.inf.n)
          (fun a b => Classical.propDecidable (a = b)) σ who s'] using
        (expect_mono μ
          (fun b => expect ((next b).evalDist
            (pureToBehavioral (@Function.update G.inf.Player
              (fun p => PureStrategy G.inf p)
              (fun a b => Classical.propDecidable (a = b)) σ who s')))
            (fun ω => G.utility ω who))
          (fun b => expect ((next b).evalDist (pureToBehavioral σ))
            (fun ω => G.utility ω who))
          (fun b => hpoint b))
    | chance b hr' =>
      exact ih b (hpi_next b) _ (ReachBy_append hreach_root (.chance b (.here _))) hr'
  | @decision p I next ih =>
    intro hroot hreach_root h u hr
    have hpi_next : ∀ a : G.inf.Act I, IsPerfectInfo (next a) :=
      fun a => IsPerfectInfo_subtree (root := .decision I next) hpi
        (.action a (.here _))
    cases hr with
    | here =>
      intro who s'
      by_cases hwho : who = p
      · -- Deviator is the deciding player
        let s'p : PureStrategy G.inf p := hwho ▸ s'
        have hUpd : Function.update σ who s' = Function.update σ p s'p := by
          cases hwho; rfl
        let aDev : G.inf.Act I := s'p I
        -- Step 1: OSD gives EU(σ, next(σ p I)) ≥ EU(σ, next(aDev))
        have hOSD : expect ((next (σ p I)).evalDist (pureToBehavioral σ))
              (fun ω => G.utility ω p) ≥
            expect ((next aDev).evalDist (pureToBehavioral σ))
              (fun ω => G.utility ω p) :=
          hnosd I next ⟨hroot, hreach_root⟩ aDev
        -- Step 2: IH gives Nash in subtree next aDev
        have hNashSub :
            (G.withTree (next aDev)).toStrategicKernelGame.IsNashFor
              (KernelGame.euPref G.toStrategicKernelGame) σ :=
          ih aDev (hpi_next aDev) _
            (ReachBy_append hreach_root (.action aDev (.here _))) (.here _)
        have hSubDev :
            expect ((next aDev).evalDist (pureToBehavioral σ)) (fun ω => G.utility ω p) ≥
            expect ((next aDev).evalDist
              (pureToBehavioral (Function.update σ p s'p)))
              (fun ω => G.utility ω p) := by
          have hb := hNashSub p s'p
          simp only [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree] at hb
          rw [update_eq_update_of_decEq] at hb
          exact hb
        -- Step 3: Evaluation at root and with deviation
        have hRootL :
            expect ((GameTree.decision I next).evalDist (pureToBehavioral σ))
              (fun ω => G.utility ω p) =
            expect ((next (σ p I)).evalDist (pureToBehavioral σ))
              (fun ω => G.utility ω p) := by
          simp [evalDist_decision, pureToBehavioral]
        have hRootR :
            expect ((GameTree.decision I next).evalDist
              (pureToBehavioral (Function.update σ p s'p)))
              (fun ω => G.utility ω p) =
            expect ((next aDev).evalDist
              (pureToBehavioral (Function.update σ p s'p)))
              (fun ω => G.utility ω p) := by
          simp [aDev, evalDist_decision, pureToBehavioral, Function.update]
        -- Chain the inequalities
        have hMain :
            expect ((GameTree.decision I next).evalDist (pureToBehavioral σ))
              (fun ω => G.utility ω p) ≥
            expect ((GameTree.decision I next).evalDist
              (pureToBehavioral (Function.update σ p s'p)))
              (fun ω => G.utility ω p) := by
          rw [hRootL, hRootR]
          exact le_trans hSubDev hOSD
        -- Bridge DecidableEq and conclude
        have hMain' :
            expect ((pureToBehavioral (Function.update σ who s') p I).bind
              (fun a => (next a).evalDist (pureToBehavioral (Function.update σ who s'))))
              (fun ω => G.utility ω p) ≤
            expect ((pureToBehavioral σ p I).bind
              (fun a => (next a).evalDist (pureToBehavioral σ)))
              (fun ω => G.utility ω p) := by
          simpa [hUpd] using hMain
        simpa [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
          hwho, update_eq_update_of_decEq (instDecidableEqFin G.inf.n)
            (fun a b => Classical.propDecidable (a = b)) σ who s'] using hMain'
      · -- Deviator is NOT the deciding player
        have hNashOpt :
            (G.withTree (next (σ p I))).toStrategicKernelGame.IsNashFor
              (KernelGame.euPref G.toStrategicKernelGame) σ :=
          ih (σ p I) (hpi_next (σ p I)) _
            (ReachBy_append hreach_root (.action (σ p I) (.here _))) (.here _)
        have hOpt := hNashOpt who s'
        have hpw : p ≠ who := Ne.symm hwho
        simpa [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
          evalDist_decision, pureToBehavioral, Function.update, hpw] using hOpt
    | action a hr' =>
      exact ih a (hpi_next a) _
        (ReachBy_append hreach_root (.action a (.here _))) hr'

set_option linter.unusedFintypeInType false in
open Classical in
/-- No profitable one-shot deviation implies SPE (for perfect-info games). -/
theorem hasNoOneShotDeviation_spe (G : EFGGame) [Fintype G.Outcome]
    (σ : PureProfile G.inf) (hpi : IsPerfectInfo G.tree)
    (hnosd : HasNoOneShotDeviation G σ) : G.IsSubgamePerfectEq σ := by
  intro t hSub
  rcases hSub.1 with ⟨hpath, hreach⟩
  have hpi_t := IsPerfectInfo_subtree hpi hreach
  exact nash_of_noOSD G σ hnosd t hpi_t hpath hreach (.here _)

-- ============================================================================
-- The equivalence
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- **One-Shot Deviation Principle**: for finite perfect-information extensive-form
    games, a pure strategy profile is a subgame-perfect equilibrium if and only if
    no player has a profitable one-shot deviation at any decision node. -/
theorem oneShotDeviation_iff_spe (G : EFGGame) [Fintype G.Outcome]
    (σ : PureProfile G.inf) (hpi : IsPerfectInfo G.tree) :
    G.IsSubgamePerfectEq σ ↔ HasNoOneShotDeviation G σ :=
  ⟨spe_hasNoOneShotDeviation G σ hpi, hasNoOneShotDeviation_spe G σ hpi⟩

end EFG
