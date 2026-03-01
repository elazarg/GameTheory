import GameTheory.EFGRefinements
import Mathlib.Tactic.Linarith

/-!
# Zermelo's Backward Induction Theorem

Every finite perfect-information extensive-form game has a subgame-perfect
equilibrium in pure strategies.

## Main definitions

- `GameTree.biEU` — backward induction expected utility of a game tree
- `GameTree.biOptAction` — the EU-maximizing action at a decision node

## Main theorems

- `evalDist_eq_of_agree` — evaluation depends only on info-sets in the tree
- `perfectInfo_disjoint_subtrees` — in perfect-info trees, sibling subtrees
  have disjoint info-sets
- `zermelo` — Zermelo's theorem: every finite perfect-info game has a pure SPE
-/

namespace EFG

open GameTheory

-- ============================================================================
-- Locality: evaluation depends only on info-sets in the tree
-- ============================================================================

/-- If two profiles agree on all info-sets appearing in a tree,
    they produce the same outcome distribution. -/
theorem evalDist_eq_of_agree {S : InfoStructure} {Outcome : Type}
    (t : GameTree S Outcome) (σ₁ σ₂ : PureProfile S)
    (hagree : ∀ (p : S.Player) (I : S.Infoset p),
      DecisionNodeIn I t → σ₁ p I = σ₂ p I) :
    t.evalDist (pureToBehavioral σ₁) = t.evalDist (pureToBehavioral σ₂) := by
  induction t with
  | terminal z => rfl
  | chance k μ hk next ih =>
    simp only [evalDist_chance]
    congr 1; funext b
    exact ih b (fun p I hIn => hagree p I (.in_chance k μ hk next b hIn))
  | decision I next ih =>
    simp only [evalDist_decision, pureToBehavioral]
    have hact : σ₁ _ I = σ₂ _ I := hagree _ I (.root next)
    rw [hact]
    congr 1; funext a
    exact ih a (fun p J hIn => hagree p J (.in_decision I next a hIn))

-- ============================================================================
-- IsPerfectInfo inherited by subtrees
-- ============================================================================

theorem IsPerfectInfo_subtree {S : InfoStructure} {Outcome : Type}
    {root : GameTree S Outcome} (hpi : IsPerfectInfo root)
    {h : List (HistoryStep S)} {t : GameTree S Outcome}
    (hreach : ReachBy h root t) : IsPerfectInfo t := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  have hr₁' := ReachBy_append hreach hr₁
  have hr₂' := ReachBy_append hreach hr₂
  obtain ⟨heq, hnext⟩ := hpi _ _ p I next₁ next₂ hr₁' hr₂'
  exact ⟨List.append_cancel_left heq, hnext⟩

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

/-- In a perfect-info decision node, the root info-set does not appear
    in any subtree. -/
theorem perfectInfo_root_not_in_subtree {S : InfoStructure} {Outcome : Type}
    {p : S.Player} {I : S.Infoset p}
    {next : S.Act I → GameTree S Outcome}
    (hpi : IsPerfectInfo (.decision I next))
    {a : S.Act I}
    (ha : DecisionNodeIn I (next a)) : False := by
  obtain ⟨ha_hist, ha_next, ha_reach⟩ := decisionNodeIn_reachBy ha
  have ra : ReachBy (HistoryStep.action p I a :: ha_hist)
      (.decision I next) (.decision I ha_next) :=
    .action a ha_reach
  have rb : ReachBy [] (.decision I next) (.decision I next) := .here _
  obtain ⟨heq, _⟩ := hpi _ _ p I ha_next next ra rb
  exact absurd heq (by simp)

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
-- Backward Induction EU
-- ============================================================================

/-- Backward induction expected utility: the payoff vector achieved by
    optimal play at each decision node. -/
noncomputable def GameTree.biEU {S : InfoStructure} {Outcome : Type}
    (u : Outcome → Payoff S.Player) :
    GameTree S Outcome → Payoff S.Player
  | .terminal z => u z
  | .chance _k μ _hk next =>
      fun p => expect μ (fun b => GameTree.biEU u (next b) p)
  | .decision (p := q) I next =>
      haveI : Nonempty (S.Act I) := ⟨⟨0, S.arity_pos q I⟩⟩
      GameTree.biEU u (next (Classical.choose
        (Finite.exists_max (fun (a : S.Act I) => GameTree.biEU u (next a) q))))

/-- The EU-maximizing action at a decision node. -/
noncomputable def biOptAction {S : InfoStructure} {Outcome : Type}
    (u : Outcome → Payoff S.Player)
    {p : S.Player} (I : S.Infoset p)
    (next : S.Act I → GameTree S Outcome) : S.Act I :=
  haveI : Nonempty (S.Act I) := ⟨⟨0, S.arity_pos p I⟩⟩
  Classical.choose (Finite.exists_max
    (fun (a : S.Act I) => GameTree.biEU u (next a) p))

theorem biOptAction_spec {S : InfoStructure} {Outcome : Type}
    (u : Outcome → Payoff S.Player)
    {p : S.Player} (I : S.Infoset p)
    (next : S.Act I → GameTree S Outcome)
    (a : S.Act I) :
    GameTree.biEU u (next a) p ≤
      GameTree.biEU u (next (biOptAction u I next)) p := by
  haveI : Nonempty (S.Act I) := ⟨a⟩
  have h := Classical.choose_spec (Finite.exists_max
    (fun (a : S.Act I) => GameTree.biEU u (next a) p))
  exact h a

-- ============================================================================
-- Transport Nash under subtree-local profile agreement
-- ============================================================================

theorem isNashFor_of_agree_on_tree {G : EFGGame}
    (t : GameTree G.inf G.Outcome) (σ τ : PureProfile G.inf)
    (hagree : ∀ (p : G.inf.Player) (I : G.inf.Infoset p),
      DecisionNodeIn I t → σ p I = τ p I)
    (hN : (G.withTree t).toStrategicKernelGame.IsNashFor
      (KernelGame.euPref G.toStrategicKernelGame) τ) :
    (G.withTree t).toStrategicKernelGame.IsNashFor
      (KernelGame.euPref G.toStrategicKernelGame) σ := by
  classical
  intro who s'
  let σu : PureProfile G.inf :=
    @Function.update G.inf.Player (fun p => PureStrategy G.inf p)
      (fun a b => Classical.propDecidable (a = b)) σ who s'
  let τu : PureProfile G.inf :=
    @Function.update G.inf.Player (fun p => PureStrategy G.inf p)
      (fun a b => Classical.propDecidable (a = b)) τ who s'
  have hEq :
      t.evalDist (pureToBehavioral σ) =
      t.evalDist (pureToBehavioral τ) :=
    evalDist_eq_of_agree t σ τ hagree
  have hEqUpd :
      t.evalDist (pureToBehavioral σu) =
      t.evalDist (pureToBehavioral τu) := by
    apply evalDist_eq_of_agree t σu τu
    intro p I hIn
    by_cases hp : p = who
    · subst hp
      simp [σu, τu]
    · simp [σu, τu, hp, hagree p I hIn]
  have hOut :
      (G.withTree t).toStrategicKernelGame.outcomeKernel σ =
      (G.withTree t).toStrategicKernelGame.outcomeKernel τ := by
    simpa [EFGGame.toStrategicKernelGame, EFGGame.withTree] using hEq
  have hNwho := hN who s'
  convert hNwho using 1

theorem isNashFor_of_agree_on_tree_symm {G : EFGGame}
    (t : GameTree G.inf G.Outcome) (σ τ : PureProfile G.inf)
    (hagree : ∀ (p : G.inf.Player) (I : G.inf.Infoset p),
      DecisionNodeIn I t → σ p I = τ p I)
    (hN : (G.withTree t).toStrategicKernelGame.IsNashFor
      (KernelGame.euPref G.toStrategicKernelGame) σ) :
    (G.withTree t).toStrategicKernelGame.IsNashFor
      (KernelGame.euPref G.toStrategicKernelGame) τ := by
  apply isNashFor_of_agree_on_tree t τ σ
  · intro p I hIn; symm; exact hagree p I hIn
  · exact hN

theorem decisionNodeIn_of_reachBy {S : InfoStructure} {Outcome : Type}
    {h : List (HistoryStep S)} {t : GameTree S Outcome}
    {p : S.Player} {I : S.Infoset p} {next : S.Act I → GameTree S Outcome}
    (hr : ReachBy h t (.decision I next)) : DecisionNodeIn I t := by
  let rec go {h : List (HistoryStep S)} {t : GameTree S Outcome}
      {p : S.Player} {I : S.Infoset p} {next : S.Act I → GameTree S Outcome}
      (hreach : ReachBy h t (.decision I next)) : DecisionNodeIn I t := by
    cases hreach with
    | here _ =>
        exact .root next
    | chance b hr' =>
        exact .in_chance _ _ _ _ b (go hr')
    | action a hr' =>
        exact .in_decision _ _ a (go hr')
  exact go hr

set_option linter.unusedFintypeInType false in
theorem expect_mono {α : Type} [Fintype α]
    (μ : PMF α) (f g : α → ℝ) (hfg : ∀ a, f a ≤ g a) :
    expect μ f ≤ expect μ g := by
  simp only [expect_eq_sum]
  exact Finset.sum_le_sum (fun a _ =>
    mul_le_mul_of_nonneg_left (hfg a) (ENNReal.toReal_nonneg))

theorem update_eq_update_of_decEq {α : Type} {β : α → Type}
    (dec₁ dec₂ : DecidableEq α) (f : (a : α) → β a) (a : α) (v : β a) :
    @Function.update α β dec₁ f a v = @Function.update α β dec₂ f a v := by
  funext i
  by_cases h : i = a
  · subst h
    simp [Function.update]
  · simp [Function.update, h]

set_option linter.unusedFintypeInType false in
theorem exists_nash_on_reachable (G : EFGGame) [Fintype G.Outcome] :
    ∀ (t : GameTree G.inf G.Outcome), IsPerfectInfo t →
      ∃ σ : PureProfile G.inf,
        ∀ {h u}, ReachBy h t u →
          (G.withTree u).toStrategicKernelGame.IsNashFor
            (KernelGame.euPref G.toStrategicKernelGame) σ := by
  intro t hpi
  induction t with
  | terminal z =>
    let σ0 : PureProfile G.inf := fun p I => ⟨0, G.inf.arity_pos p I⟩
    refine ⟨σ0, ?_⟩
    intro h u hr
    cases hr
    simpa [σ0] using terminal_isNashFor_euPref (G := G) z σ0
  | chance k μ hk next ih =>
    classical
    have hpi_next : ∀ b : Fin k, IsPerfectInfo (next b) := by
      intro b
      exact IsPerfectInfo_subtree (root := .chance k μ hk next) hpi
        (.chance b (.here _))
    choose σChild hAllChild using (fun b => ih b (hpi_next b))
    let b0 : Fin k := ⟨0, hk⟩
    let pick : (q : G.inf.Player) → (J : G.inf.Infoset q) → Fin k :=
      fun q J =>
        if hJ : ∃ b, DecisionNodeIn J (next b) then Classical.choose hJ else b0
    let σ : PureProfile G.inf := fun q J => (σChild (pick q J)) q J
    have hagree_next : ∀ (b : Fin k) (q : G.inf.Player) (J : G.inf.Infoset q),
        DecisionNodeIn J (next b) → σ q J = σChild b q J := by
      intro b q J hIn
      unfold σ pick
      by_cases hJ : ∃ c, DecisionNodeIn J (next c)
      · simp [hJ]
        have hch : DecisionNodeIn J (next (Classical.choose hJ)) :=
          Classical.choose_spec hJ
        have hbc : Classical.choose hJ = b := by
          by_contra hneq
          exact perfectInfo_disjoint_chance_subtrees (hpi := hpi) hneq hch hIn
        simp [hbc]
      · exact (False.elim (hJ ⟨b, hIn⟩))
    have hNnext : ∀ b : Fin k,
        (G.withTree (next b)).toStrategicKernelGame.IsNashFor
          (KernelGame.euPref G.toStrategicKernelGame) σ := by
      intro b
      have hNb_child :
          (G.withTree (next b)).toStrategicKernelGame.IsNashFor
            (KernelGame.euPref G.toStrategicKernelGame) (σChild b) :=
        hAllChild b (.here _)
      exact isNashFor_of_agree_on_tree (G := G) (next b) σ (σChild b)
        (fun q J hIn => hagree_next b q J hIn) hNb_child
    refine ⟨σ, ?_⟩
    intro h u hr
    cases hr with
    | here =>
      intro who s'
      let σu : PureProfile G.inf :=
        @Function.update G.inf.Player (fun p => PureStrategy G.inf p)
          (fun a b => Classical.propDecidable (a = b)) σ who s'
      have hσu : Function.update σ who s' = σu := by
        funext i
        by_cases hi : i = who
        · subst hi
          simp [σu, Function.update]
        · simp [σu, Function.update, hi]
      have hpoint :
          ∀ b : Fin k,
            expect ((next b).evalDist (pureToBehavioral σ)) (fun ω => G.utility ω who) ≥
            expect ((next b).evalDist (pureToBehavioral σu)) (fun ω => G.utility ω who) := by
        intro b
        have hb := hNnext b who s'
        simpa [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree] using hb
      simpa [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
        evalDist_chance, expect_bind, hσu] using
        (expect_mono μ
          (fun b => expect ((next b).evalDist (pureToBehavioral σu))
            (fun ω => G.utility ω who))
          (fun b => expect ((next b).evalDist (pureToBehavioral σ))
            (fun ω => G.utility ω who))
          (fun b => hpoint b))
    | chance b hr' =>
      have hNu_child :
          (G.withTree u).toStrategicKernelGame.IsNashFor
            (KernelGame.euPref G.toStrategicKernelGame) (σChild b) :=
        hAllChild b hr'
      have hagree_u : ∀ (q : G.inf.Player) (J : G.inf.Infoset q),
          DecisionNodeIn J u → σ q J = σChild b q J := by
        intro q J hInU
        obtain ⟨hist, nextJ, hReachU⟩ := decisionNodeIn_reachBy hInU
        have hInB : DecisionNodeIn J (next b) :=
          decisionNodeIn_of_reachBy (ReachBy_append hr' hReachU)
        exact hagree_next b q J hInB
      exact isNashFor_of_agree_on_tree (G := G) u σ (σChild b) hagree_u hNu_child
  | @decision p I next ih =>
    classical
    have hpi_next : ∀ a : G.inf.Act I, IsPerfectInfo (next a) := by
      intro a
      exact IsPerfectInfo_subtree (root := .decision I next) hpi
        (.action a (.here _))
    choose σChild hAllChild using (fun a => ih a (hpi_next a))
    let V : G.inf.Act I → ℝ :=
      fun a => expect ((next a).evalDist (pureToBehavioral (σChild a)))
        (fun ω => G.utility ω p)
    haveI : Nonempty (G.inf.Act I) := ⟨⟨0, G.inf.arity_pos p I⟩⟩
    let aOpt : G.inf.Act I := Classical.choose (Finite.exists_max V)
    have hVmax : ∀ a, V a ≤ V aOpt := Classical.choose_spec (Finite.exists_max V)
    let pick : (q : G.inf.Player) → (J : G.inf.Infoset q) → G.inf.Act I :=
      fun q J =>
        if hJ : ∃ a, DecisionNodeIn J (next a) then Classical.choose hJ else aOpt
    let σbase : PureProfile G.inf := fun q J => (σChild (pick q J)) q J
    let sp : PureStrategy G.inf p := Function.update (σbase p) I aOpt
    let σ : PureProfile G.inf := Function.update σbase p sp
    have hagree_next : ∀ (a : G.inf.Act I) (q : G.inf.Player) (J : G.inf.Infoset q),
        DecisionNodeIn J (next a) → σ q J = σChild a q J := by
      intro a q J hIn
      have hσbase : σ q J = σbase q J := by
        by_cases hq : q = p
        · subst hq
          have hJI : J ≠ I := by
            exact fun hEq => perfectInfo_root_not_in_subtree (hpi := hpi) (hEq ▸ hIn)
          simp [σ, sp, σbase, Function.update, hJI]
        · simp [σ, sp, σbase, hq]
      rw [hσbase]
      unfold σbase pick
      by_cases hJ : ∃ b, DecisionNodeIn J (next b)
      · simp [hJ]
        have hch : DecisionNodeIn J (next (Classical.choose hJ)) :=
          Classical.choose_spec hJ
        have hba : Classical.choose hJ = a := by
          by_contra hneq
          exact perfectInfo_disjoint_subtrees (hpi := hpi) hneq hch hIn
        simp [hba]
      · exact (False.elim (hJ ⟨a, hIn⟩))
    have hNnext : ∀ a : G.inf.Act I,
        (G.withTree (next a)).toStrategicKernelGame.IsNashFor
          (KernelGame.euPref G.toStrategicKernelGame) σ := by
      intro a
      have hNa_child :
          (G.withTree (next a)).toStrategicKernelGame.IsNashFor
            (KernelGame.euPref G.toStrategicKernelGame) (σChild a) :=
        hAllChild a (.here _)
      exact isNashFor_of_agree_on_tree (G := G) (next a) σ (σChild a)
        (fun q J hIn => hagree_next a q J hIn) hNa_child
    have hValEq : ∀ a : G.inf.Act I,
        expect ((next a).evalDist (pureToBehavioral σ)) (fun ω => G.utility ω p) = V a := by
      intro a
      have hEqA :
          (next a).evalDist (pureToBehavioral σ) =
          (next a).evalDist (pureToBehavioral (σChild a)) :=
        evalDist_eq_of_agree (next a) σ (σChild a)
          (fun q J hIn => hagree_next a q J hIn)
      simp [V, hEqA]
    refine ⟨σ, ?_⟩
    intro h u hr
    cases hr with
    | here =>
      intro who s'
      by_cases hwho : who = p
      · let s'p : PureStrategy G.inf p := hwho ▸ s'
        have hUpd : Function.update σ who s' = Function.update σ p s'p := by
          cases hwho
          rfl
        let σpc : PureProfile G.inf :=
          @Function.update G.inf.Player (fun r => PureStrategy G.inf r)
            (fun a b => Classical.propDecidable (a = b)) σ p s'p
        have hUpdDec : Function.update σ p s'p = σpc := by
          funext i
          by_cases hi : i = p
          · subst hi
            simp [σpc, Function.update]
          · simp [σpc, Function.update, hi]
        let aDev : G.inf.Act I := s'p I
        have hSubDev :
            expect ((next aDev).evalDist (pureToBehavioral σ)) (fun ω => G.utility ω p) ≥
            expect
              ((next aDev).evalDist (pureToBehavioral (Function.update σ p s'p)))
              (fun ω => G.utility ω p) := by
          have hD := hNnext aDev p s'p
          simpa [KernelGame.euPref, EFGGame.toStrategicKernelGame,
            EFGGame.withTree, hUpdDec] using hD
        have hMain :
            expect ((GameTree.decision I next).evalDist (pureToBehavioral σ))
              (fun ω => G.utility ω p) ≥
            expect ((GameTree.decision I next).evalDist
              (pureToBehavioral (Function.update σ p s'p)))
              (fun ω => G.utility ω p) := by
          have hRootL :
              expect ((GameTree.decision I next).evalDist (pureToBehavioral σ))
                (fun ω => G.utility ω p) =
              expect ((next aOpt).evalDist (pureToBehavioral σ))
                (fun ω => G.utility ω p) := by
            simp [evalDist_decision, pureToBehavioral, σ, sp, Function.update]
          have hRootR :
              expect ((GameTree.decision I next).evalDist
                (pureToBehavioral (Function.update σ p s'p)))
                (fun ω => G.utility ω p) =
              expect ((next aDev).evalDist
                (pureToBehavioral (Function.update σ p s'p)))
                (fun ω => G.utility ω p) := by
            simp [aDev, evalDist_decision, pureToBehavioral, σ, sp, Function.update]
          rw [hRootL, hRootR]
          calc
            expect ((next aOpt).evalDist (pureToBehavioral σ))
              (fun ω => G.utility ω p) = V aOpt := hValEq aOpt
            _ ≥ V aDev := hVmax aDev
            _ = expect ((next aDev).evalDist (pureToBehavioral σ))
                (fun ω => G.utility ω p) := (hValEq aDev).symm
            _ ≥ expect ((next aDev).evalDist
                (pureToBehavioral (Function.update σ p s'p)))
                (fun ω => G.utility ω p) := hSubDev
        have hMain' :
            expect ((pureToBehavioral (Function.update σ who s') p I).bind
              (fun a => (next a).evalDist (pureToBehavioral (Function.update σ who s'))))
              (fun ω => G.utility ω p) ≤
            expect ((pureToBehavioral σ p I).bind
              (fun a => (next a).evalDist (pureToBehavioral σ)))
              (fun ω => G.utility ω p) := by
          simpa [hUpd] using hMain
        have hUpdWhoDec :
            @Function.update (Fin G.inf.n) (fun r => PureStrategy G.inf r)
              (instDecidableEqFin G.inf.n) σ who s' =
            @Function.update G.inf.Player (fun r => PureStrategy G.inf r)
              (fun a b => Classical.propDecidable (a = b)) σ who s' :=
          update_eq_update_of_decEq
            (instDecidableEqFin G.inf.n) (fun a b => Classical.propDecidable (a = b))
            σ who s'
        simpa [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
          hwho, hUpdWhoDec] using hMain'
      · have hOpt := hNnext aOpt who s'
        have hpw : p ≠ who := by exact Ne.symm hwho
        simpa [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
          evalDist_decision, pureToBehavioral, σ, sp, Function.update, hpw] using hOpt
    | action a hr' =>
      have hNu_child :
          (G.withTree u).toStrategicKernelGame.IsNashFor
            (KernelGame.euPref G.toStrategicKernelGame) (σChild a) :=
        hAllChild a hr'
      have hagree_u : ∀ (q : G.inf.Player) (J : G.inf.Infoset q),
          DecisionNodeIn J u → σ q J = σChild a q J := by
        intro q J hInU
        obtain ⟨hist, nextJ, hReachU⟩ := decisionNodeIn_reachBy hInU
        have hInA : DecisionNodeIn J (next a) :=
          decisionNodeIn_of_reachBy (ReachBy_append hr' hReachU)
        exact hagree_next a q J hInA
      exact isNashFor_of_agree_on_tree (G := G) u σ (σChild a) hagree_u hNu_child

-- ============================================================================
-- Zermelo's Theorem
-- ============================================================================

set_option linter.unusedFintypeInType false

/-- **Zermelo's Backward Induction Theorem**: every finite perfect-information
    extensive-form game has a pure subgame-perfect equilibrium.

    The proof proceeds by structural induction on the game tree:
    - Terminal nodes are trivially Nash for any profile.
    - At decision nodes, by induction each subtree has an SPE; the deciding
      player picks the action maximizing their EU, yielding an SPE for the
      whole subtree.
    - At chance nodes, induction provides SPEs for all branches. -/
theorem zermelo (G : EFGGame) [Fintype G.Outcome]
    (hpi : IsPerfectInfo G.tree) :
    ∃ σ : PureProfile G.inf, G.IsSubgamePerfectEq σ := by
  obtain ⟨σ, hReachNash⟩ := exists_nash_on_reachable G G.tree hpi
  refine ⟨σ, ?_⟩
  intro t hSub
  rcases hSub.1 with ⟨h, hReach⟩
  exact hReachNash hReach

set_option linter.unusedFintypeInType true

end EFG
