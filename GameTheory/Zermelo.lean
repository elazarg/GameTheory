import GameTheory.OneShotDeviation

/-!
# Zermelo's Backward Induction Theorem

Every finite perfect-information extensive-form game has a subgame-perfect
equilibrium in pure strategies.

The proof constructs a profile with no profitable one-shot deviation via
backward induction, then applies the one-shot deviation principle.

## Main theorems

- `perfectInfo_disjoint_subtrees` — in perfect-info trees, sibling subtrees
  have disjoint info-sets
- `exists_noOSD` — backward induction constructs a profile with no
  profitable one-shot deviation
- `zermelo` — Zermelo's theorem: every finite perfect-info game has a pure SPE,
  derived as a corollary of the one-shot deviation principle
-/

namespace EFG

open GameTheory

-- ============================================================================
-- Disjointness of info-sets in sibling subtrees (perfect info)
-- ============================================================================

/-- In a perfect-info decision node, an info-set cannot appear in two
    different sibling subtrees. -/
theorem perfectInfo_disjoint_subtrees {S : InfoStructure} {Outcome : Type}
    {p : S.Player} {I : S.Infoset p}
    {next : S.Act I → GameTree S Outcome}
    (hpi : IsPerfectInfo (.decision I next))
    {q : S.Player} {J : S.Infoset q}
    {a b : S.Act I} (hab : a ≠ b)
    (ha : DecisionNodeIn J (next a))
    (hb : DecisionNodeIn J (next b)) : False := by
  obtain ⟨ha_hist, ha_next, ha_reach⟩ := decisionNodeIn_reachBy ha
  obtain ⟨hb_hist, hb_next, hb_reach⟩ := decisionNodeIn_reachBy hb
  have ra : ReachBy (HistoryStep.action p I a :: ha_hist)
      (.decision I next) (.decision J ha_next) :=
    .action a ha_reach
  have rb : ReachBy (HistoryStep.action p I b :: hb_hist)
      (.decision I next) (.decision J hb_next) :=
    .action b hb_reach
  obtain ⟨heq, _⟩ := hpi _ _ q J ha_next hb_next ra rb
  have h := (List.cons.inj heq).1
  simp only [HistoryStep.action.injEq, heq_eq_eq, true_and] at h
  exact hab h

/-- In a perfect-info chance node, an info-set cannot appear in two
    different chance branches. -/
theorem perfectInfo_disjoint_chance_subtrees {S : InfoStructure} {Outcome : Type}
    {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome}
    (hpi : IsPerfectInfo (.chance k μ hk next))
    {q : S.Player} {J : S.Infoset q}
    {b c : Fin k} (hbc : b ≠ c)
    (hb : DecisionNodeIn J (next b))
    (hc : DecisionNodeIn J (next c)) : False := by
  obtain ⟨hb_hist, hb_next, hb_reach⟩ := decisionNodeIn_reachBy hb
  obtain ⟨hc_hist, hc_next, hc_reach⟩ := decisionNodeIn_reachBy hc
  have rb : ReachBy (HistoryStep.chance k b :: hb_hist)
      (.chance k μ hk next) (.decision J hb_next) := .chance b hb_reach
  have rc : ReachBy (HistoryStep.chance k c :: hc_hist)
      (.chance k μ hk next) (.decision J hc_next) := .chance c hc_reach
  obtain ⟨heq, _⟩ := hpi _ _ q J hb_next hc_next rb rc
  have h := (List.cons.inj heq).1
  have hbceq : b = c := by simpa using h
  exact hbc hbceq

-- ============================================================================
-- Backward induction constructs a profile with no one-shot deviations
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- Backward induction constructs a pure strategy profile that has no
    profitable one-shot deviation at any decision node in the tree.
    This is the constructive core of Zermelo's theorem. -/
theorem exists_noOSD (G : EFGGame) [Fintype G.Outcome] :
    ∀ (t : GameTree G.inf G.Outcome), IsPerfectInfo t →
      ∃ σ : PureProfile G.inf,
        ∀ {q : G.inf.Player} (J : G.inf.Infoset q)
          (nextJ : G.inf.Act J → GameTree G.inf G.Outcome),
          (∃ h, ReachBy h t (.decision J nextJ)) →
          ∀ (a' : G.inf.Act J),
            expect ((nextJ (σ q J)).evalDist (pureToBehavioral σ))
              (fun ω => G.utility ω q) ≥
            expect ((nextJ a').evalDist (pureToBehavioral σ))
              (fun ω => G.utility ω q) := by
  intro t hpi
  induction t with
  | terminal z =>
    refine ⟨fun p I => ⟨0, G.inf.arity_pos p I⟩, ?_⟩
    intro q J nextJ ⟨_, hr⟩ _
    cases hr
  | chance k μ hk next ih =>
    classical
    have hpi_next : ∀ b : Fin k, IsPerfectInfo (next b) :=
      fun b => IsPerfectInfo_subtree (root := .chance k μ hk next) hpi (.chance b (.here _))
    choose σChild hAllChild using (fun b => ih b (hpi_next b))
    let b0 : Fin k := ⟨0, hk⟩
    let pick : (r : G.inf.Player) → (K : G.inf.Infoset r) → Fin k :=
      fun r K =>
        if hJ : ∃ b, DecisionNodeIn K (next b) then Classical.choose hJ else b0
    let σ : PureProfile G.inf := fun r K => (σChild (pick r K)) r K
    have hagree_next : ∀ (b : Fin k) (r : G.inf.Player) (K : G.inf.Infoset r),
        DecisionNodeIn K (next b) → σ r K = σChild b r K := by
      intro b r K hIn
      unfold σ pick
      by_cases hJ : ∃ c, DecisionNodeIn K (next c)
      · simp [hJ]
        have hch : DecisionNodeIn K (next (Classical.choose hJ)) :=
          Classical.choose_spec hJ
        have hbc : Classical.choose hJ = b := by
          by_contra hneq
          exact perfectInfo_disjoint_chance_subtrees (hpi := hpi) hneq hch hIn
        simp [hbc]
      · exact (False.elim (hJ ⟨b, hIn⟩))
    refine ⟨σ, ?_⟩
    intro q J nextJ ⟨h, hreach⟩ a'
    cases hreach with
    | chance b hr' =>
      -- Transfer OSD from σChild b to σ
      have hactJ : σ q J = σChild b q J :=
        hagree_next b q J (decisionNodeIn_of_reachBy hr')
      have heval : ∀ x, (nextJ x).evalDist (pureToBehavioral σ) =
          (nextJ x).evalDist (pureToBehavioral (σChild b)) := by
        intro x
        apply evalDist_eq_of_agree
        intro r K hInK
        apply hagree_next b
        obtain ⟨histK, nextK, hReachK⟩ := decisionNodeIn_reachBy hInK
        exact decisionNodeIn_of_reachBy
          (ReachBy_append (ReachBy_append hr' (.action x (.here _))) hReachK)
      rw [hactJ, heval (σChild b q J), heval a']
      exact hAllChild b J nextJ ⟨_, hr'⟩ a'
  | @decision p I next ih =>
    classical
    have hpi_next : ∀ a : G.inf.Act I, IsPerfectInfo (next a) :=
      fun a => IsPerfectInfo_subtree (root := .decision I next) hpi (.action a (.here _))
    choose σChild hAllChild using (fun a => ih a (hpi_next a))
    let V : G.inf.Act I → ℝ :=
      fun a => expect ((next a).evalDist (pureToBehavioral (σChild a)))
        (fun ω => G.utility ω p)
    haveI : Nonempty (G.inf.Act I) := ⟨⟨0, G.inf.arity_pos p I⟩⟩
    let aOpt : G.inf.Act I := Classical.choose (Finite.exists_max V)
    have hVmax : ∀ a, V a ≤ V aOpt := Classical.choose_spec (Finite.exists_max V)
    let pick : (r : G.inf.Player) → (K : G.inf.Infoset r) → G.inf.Act I :=
      fun r K =>
        if hJ : ∃ a, DecisionNodeIn K (next a) then Classical.choose hJ else aOpt
    let σbase : PureProfile G.inf := fun r K => (σChild (pick r K)) r K
    let sp : PureStrategy G.inf p := Function.update (σbase p) I aOpt
    let σ : PureProfile G.inf := Function.update σbase p sp
    have hagree_next : ∀ (a : G.inf.Act I) (r : G.inf.Player) (K : G.inf.Infoset r),
        DecisionNodeIn K (next a) → σ r K = σChild a r K := by
      intro a r K hIn
      have hσbase : σ r K = σbase r K := by
        by_cases hr : r = p
        · subst hr
          have hKI : K ≠ I :=
            fun hEq => perfectInfo_root_not_in_subtree (hpi := hpi) (hEq ▸ hIn)
          simp [σ, sp, σbase, Function.update, hKI]
        · simp [σ, sp, σbase, hr]
      rw [hσbase]
      unfold σbase pick
      by_cases hJ : ∃ b, DecisionNodeIn K (next b)
      · simp [hJ]
        have hch : DecisionNodeIn K (next (Classical.choose hJ)) :=
          Classical.choose_spec hJ
        have hba : Classical.choose hJ = a := by
          by_contra hneq
          exact perfectInfo_disjoint_subtrees (hpi := hpi) hneq hch hIn
        simp [hba]
      · exact (False.elim (hJ ⟨a, hIn⟩))
    have hValEq : ∀ a : G.inf.Act I,
        expect ((next a).evalDist (pureToBehavioral σ)) (fun ω => G.utility ω p) = V a := by
      intro a
      have hEqA : (next a).evalDist (pureToBehavioral σ) =
          (next a).evalDist (pureToBehavioral (σChild a)) :=
        evalDist_eq_of_agree (next a) σ (σChild a) (fun r K hIn => hagree_next a r K hIn)
      simp [V, hEqA]
    have hσI : σ p I = aOpt := by simp [σ, sp, Function.update]
    refine ⟨σ, ?_⟩
    intro q J nextJ ⟨h, hreach⟩ a'
    cases hreach with
    | here =>
      -- Root decision node: q=p, J=I, nextJ=next
      -- OSD: V(aOpt) ≥ V(a')
      rw [hσI, hValEq aOpt, hValEq a']
      exact hVmax a'
    | action a hr' =>
      -- Subtree: transfer OSD from σChild a to σ
      have hactJ : σ q J = σChild a q J :=
        hagree_next a q J (decisionNodeIn_of_reachBy hr')
      have heval : ∀ x, (nextJ x).evalDist (pureToBehavioral σ) =
          (nextJ x).evalDist (pureToBehavioral (σChild a)) := by
        intro x
        apply evalDist_eq_of_agree
        intro r K hInK
        apply hagree_next a
        obtain ⟨histK, nextK, hReachK⟩ := decisionNodeIn_reachBy hInK
        exact decisionNodeIn_of_reachBy
          (ReachBy_append (ReachBy_append hr' (.action x (.here _))) hReachK)
      rw [hactJ, heval (σChild a q J), heval a']
      exact hAllChild a J nextJ ⟨_, hr'⟩ a'

-- ============================================================================
-- Zermelo's Theorem
-- ============================================================================

set_option linter.unusedFintypeInType false

/-- **Zermelo's Backward Induction Theorem**: every finite perfect-information
    extensive-form game has a pure subgame-perfect equilibrium.

    The proof constructs a profile with no profitable one-shot deviation via
    backward induction (`exists_noOSD`), then applies the one-shot deviation
    principle (`oneShotDeviation_iff_spe`) to conclude SPE. -/
theorem zermelo (G : EFGGame) [Fintype G.Outcome]
    (hpi : IsPerfectInfo G.tree) :
    ∃ σ : PureProfile G.inf, G.IsSubgamePerfectEq σ := by
  obtain ⟨σ, hOSD⟩ := exists_noOSD G G.tree hpi
  exact ⟨σ, (oneShotDeviation_iff_spe G σ hpi).mpr hOSD⟩

set_option linter.unusedFintypeInType true

end EFG
