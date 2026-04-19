import GameTheory.Languages.Sequential.CompileObsLin

/-!
# Adequacy for Linearized Compilation

Pure and behavioral adequacy theorems: running the linearized compiled model
matches `Protocol.eval` (pure) and `Protocol.evalMixed` (behavioral).

## Main results

- `runDistPure_eq_eval` — pure adequacy
- `runDist_liftBehavioral_extractState_eq_evalMixed` — behavioral adequacy
-/

namespace GameTheory.Sequential

open GameTheory

variable {n : Nat} {S V A Sig : Type}

-- ============================================================================
-- Adequacy: linearized execution matches protocol evaluation
-- ============================================================================

section Adequacy

variable {G : Protocol n S V A Sig} [DecidableEq (Fin n)] [Fintype (Fin n)]

-- [Fintype (Fin n)] is needed for runDistPure_eq_eval to unify with
-- downstream callers that have [Fintype (Fin n)] section variables.
-- Many intermediate lemmas don't use it directly.
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-- The final state of a `LinConfig`. For `terminal s`, this is `s`.
For non-terminal configurations, this is the current state carried
by the configuration (evaluation not yet complete). -/
def LinConfig.state : LinConfig G → S
  | .signal _ s => s
  | .playerTurn _ s _ _ _ => s
  | .applyTransition _ s _ _ => s
  | .terminal s => s

/-- Resolve players `pVal, pVal+1, ..., n-1` at round `k`, accumulating actions,
then transition and continue from round `k+1`.

This is the "semantic backbone" for adequacy: it evaluates the protocol by
resolving one player at a time, matching the linearized model's step structure. -/
noncomputable def evalLinearized (G : Protocol n S V A Sig)
    (σ : PureProfile n V A)
    (rounds : List (Round n S V A Sig))
    (s : S) : PMF S :=
  match rounds with
  | [] => PMF.pure s
  | r :: rest =>
    (r.signal s).bind fun sig =>
      let acts : Fin n → Option A := fun i => σ i (r.view i s (sig i))
      let next := r.transition s acts
      evalLinearized G σ rest next

omit [DecidableEq (Fin n)] in
private theorem pmf_foldl_bind
    (f : Round n S V A Sig → PureProfile n V A → S → PMF S)
    (σ : PureProfile n V A) (μ : PMF S) (rest : List (Round n S V A Sig)) :
    rest.foldl (fun dist r => dist.bind (f r σ)) μ =
      μ.bind (fun s => rest.foldl (fun dist r => dist.bind (f r σ)) (PMF.pure s)) := by
  induction rest generalizing μ with
  | nil => simp
  | cons r' rest' ih =>
    simp only [List.foldl_cons]
    rw [ih, PMF.bind_bind]
    congr 1
    ext s
    rw [PMF.pure_bind, ih]

omit [DecidableEq (Fin n)] in
private theorem evalRounds_cons (r : Round n S V A Sig)
    (rest : List (Round n S V A Sig)) (σ : PureProfile n V A) (s : S) :
    evalRounds (r :: rest) σ s = (r.eval σ s).bind (evalRounds rest σ) := by
  simp only [evalRounds, List.foldl_cons]
  rw [PMF.pure_bind]
  exact pmf_foldl_bind Round.eval σ (r.eval σ s) rest

omit [DecidableEq (Fin n)] in
set_option linter.unusedFintypeInType false in
private theorem pmf_foldl_bind_mixed [Fintype (Option A)]
    (f : Round n S V A Sig → BehavioralProfile n V A → S → PMF S)
    (σ : BehavioralProfile n V A) (μ : PMF S) (rest : List (Round n S V A Sig)) :
    rest.foldl (fun dist r => dist.bind (f r σ)) μ =
      μ.bind (fun s => rest.foldl (fun dist r => dist.bind (f r σ)) (PMF.pure s)) := by
  induction rest generalizing μ with
  | nil => simp
  | cons r' rest' ih =>
    simp only [List.foldl_cons]
    rw [ih, PMF.bind_bind]
    congr 1
    ext s
    rw [PMF.pure_bind, ih]

omit [DecidableEq (Fin n)] in
set_option linter.unusedFintypeInType false in
private theorem evalRoundsMixed_cons [Fintype (Option A)] (r : Round n S V A Sig)
    (rest : List (Round n S V A Sig)) (σ : BehavioralProfile n V A) (s : S) :
    evalRoundsMixed (r :: rest) σ s = (r.evalMixed σ s).bind (evalRoundsMixed rest σ) := by
  simp only [evalRoundsMixed, List.foldl_cons]
  rw [PMF.pure_bind]
  exact pmf_foldl_bind_mixed Round.evalMixed σ (r.evalMixed σ s) rest

omit [DecidableEq (Fin n)] in
private theorem evalLinearized_eq_evalRounds (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (rounds : List (Round n S V A Sig)) (s : S) :
    evalLinearized G σ rounds s = evalRounds rounds σ s := by
  induction rounds generalizing s with
  | nil => simp [evalLinearized, evalRounds]
  | cons r rest ih =>
    rw [evalRounds_cons]
    simp only [evalLinearized, Round.eval, PMF.map]
    conv_rhs => rw [PMF.bind_bind]
    congr 1
    ext sig
    simp only [Function.comp, PMF.pure_bind]
    exact congrFun (congrArg DFunLike.coe (ih _)) _

omit [DecidableEq (Fin n)] in
theorem evalLinearized_eq_eval (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) :
    evalLinearized G σ G.rounds G.init = G.eval σ :=
  evalLinearized_eq_evalRounds G σ G.rounds G.init

/-- Resolve players `pVal, pVal+1, ..., n-1` with pure strategies, accumulating
their actions. Returns the fully populated action vector. -/
def resolveActions (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) (pVal : Nat) (accActs : Fin n → Option A) :
    Fin n → Option A :=
  if hp : pVal < n then
    let p : Fin n := ⟨pVal, hp⟩
    resolveActions G σ r s sig (pVal + 1)
      (Function.update accActs p (σ p (r.view p s (sig p))))
  else
    accActs
  termination_by (n - pVal)

/-- After resolving players from `pVal` onward, the accumulated actions for
players `< pVal` are unchanged and players `≥ pVal` get their strategy values. -/
private theorem resolveActions_spec (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) (pVal : Nat) (accActs : Fin n → Option A)
    (h_below : ∀ i : Fin n, i.val < pVal → accActs i = σ i (r.view i s (sig i))) :
    resolveActions G σ r s sig pVal accActs =
      fun i => σ i (r.view i s (sig i)) := by
  unfold resolveActions
  split
  case isTrue hp =>
    apply resolveActions_spec
    intro i hi
    by_cases hpi : i = ⟨pVal, hp⟩
    · subst hpi; simp [Function.update_self]
    · rw [Function.update_of_ne hpi]
      exact h_below i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) (by
        intro heq; exact hpi (Fin.ext heq)))
  case isFalse hp =>
    funext i
    exact h_below i (by omega)
  termination_by (n - pVal)

/-- After resolving all players from 0, the accumulated actions equal the
simultaneous action vector. -/
theorem resolveActions_eq (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) :
    resolveActions G σ r s sig 0 (fun _ => none) =
      fun i => σ i (r.view i s (sig i)) :=
  resolveActions_spec G σ r s sig 0 _ (fun i hi => absurd hi (by omega))

/-- Evaluate from a `LinConfig` using a pure profile. Non-recursive: dispatches
to `evalLinearized` on the remaining rounds.

- **Signal k s**: evaluate rounds from k onward
- **PlayerTurn k s sig p accActs**: resolve remaining players, then evaluate from k+1
- **Terminal s**: point mass on s -/
noncomputable def evalFromCfg (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) : LinConfig G → PMF S
  | .terminal s => PMF.pure s
  | .signal k s => evalLinearized G σ (G.rounds.drop k) s
  | .playerTurn k s sig p accActs =>
    match G.rounds[k]? with
    | some r =>
      let fullActs := resolveActions G σ r s sig p.val accActs
      let next := r.transition s fullActs
      evalLinearized G σ (G.rounds.drop (k + 1)) next
    | none => PMF.pure s
  | .applyTransition k s _sig accActs =>
    match G.rounds[k]? with
    | some r =>
      let next := r.transition s accActs
      evalLinearized G σ (G.rounds.drop (k + 1)) next
    | none => PMF.pure s

/-- `evalFromCfg` at the initial configuration equals `Protocol.eval`. -/
theorem evalFromCfg_init (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) :
    evalFromCfg G σ (linInitialConfig G) = G.eval σ := by
  simp only [linInitialConfig]
  split <;> simp only [evalFromCfg]
  · -- G.rounds[0]? = none → rounds is empty → terminal case
    rename_i h
    have hnil : G.rounds = [] := by
      match hr : G.rounds with
      | [] => rfl
      | _ :: _ => simp [hr] at h
    simp [Protocol.eval, evalRounds, hnil]
  · -- G.rounds[0]? ≠ none → signal case
    rw [List.drop_zero]
    exact evalLinearized_eq_eval G σ

/-- `extractPlayerAction` with `liftPureProfile` gives the protocol-level action. -/
private theorem extractPlayerAction_lift (σ : PureProfile n V A)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n)
    (accActs : Fin n → Option A) (r : Round n S V A Sig)
    (hr : G.rounds[k]? = some r) :
    extractPlayerAction G k s sig p accActs
      (fun i => (liftPureProfile (G := G) σ) i
        (linObserve G i (.playerTurn k s sig p accActs))) =
    σ p (r.view p s (sig p)) := by
  unfold extractPlayerAction
  have hk : k < G.rounds.length := by
    by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
  split
  case isTrue hk' =>
    have hobs : linObserve G p (.playerTurn k s sig p accActs) =
        some (⟨k, hk'⟩, G.rounds[k].view p s (sig p)) := by simp [linObserve, hk']
    have hr' : G.rounds[k] = r := by
      have := List.getElem?_eq_getElem hk' ▸ hr; exact Option.some.inj this
    change cast _ _ = _
    rw [cast_eq_iff_heq]
    simp only [liftPureProfile, liftLocalStrategy]
    rw [hobs, hr']
    rfl
  case isFalse hk' =>
    exact absurd hk hk'

/-- One step of the linearized model composed with `evalFromCfg` telescopes:
performing one step and then evaluating from the resulting configuration gives
the same result as evaluating from the current configuration. -/
private theorem stepPMF_bind_evalFromCfg
    (σ : PureProfile n V A) (cfg : LinConfig G) :
    (linConfigStepPMF G cfg
      (fun i => (liftPureProfile (G := G) σ) i (linObserve G i cfg))).bind
        (evalFromCfg G σ) =
    evalFromCfg G σ cfg := by
  cases cfg with
  | terminal s =>
    -- Step at terminal is PMF.pure (.terminal s), identity
    simp [linConfigStepPMF, evalFromCfg, PMF.pure_bind]
  | signal k s =>
    -- Step samples signal and creates playerTurn (or transitions if n=0)
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      split
      case isTrue hn =>
        -- n > 0: signal → playerTurn 0
        -- LHS: (r.signal s).map (fun sig => .playerTurn k s sig ⟨0, hn⟩ (fun _ => none))
        --        .bind (evalFromCfg G σ)
        -- = (r.signal s).bind (fun sig => evalFromCfg G σ (.playerTurn ...))
        rw [PMF.bind_map]
        -- Unfold evalFromCfg at the playerTurn
        simp only [Function.comp_def, evalFromCfg, hr]
        -- RHS: evalLinearized G σ (G.rounds.drop k) s
        -- Since G.rounds[k]? = some r, drop k = r :: drop (k+1)
        have hk : k < G.rounds.length := by
          by_contra h; push_neg at h
          simp [List.getElem?_eq_none (by omega)] at hr
        have hdrop : G.rounds.drop k = r :: G.rounds.drop (k + 1) := by
          rw [← List.cons_getElem_drop_succ (h := hk)]
          congr 1; exact (List.getElem_of_getElem? hr).choose_spec
        rw [hdrop, evalLinearized]
        congr 1; ext sig; simp only []
        rw [resolveActions_eq]
      case isFalse hn =>
        have h0 : n = 0 := by omega
        subst h0
        have hempty : ∀ (f g : Fin 0 → Option A), f = g :=
          fun f g => funext fun i => absurd i.pos hn
        have hk : k < G.rounds.length := by
          by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
        have hdrop : G.rounds.drop k = r :: G.rounds.drop (k + 1) := by
          rw [← List.cons_getElem_drop_succ (h := hk)]
          congr 1; exact (List.getElem_of_getElem? hr).choose_spec
        -- LHS: (r.signal s).map (.applyTransition k s · (fun _ => none)).bind (evalFromCfg G σ)
        rw [PMF.bind_map]
        -- Unfold evalFromCfg at .applyTransition
        simp only [Function.comp_def, evalFromCfg, hr]
        -- RHS: evalLinearized G σ (G.rounds.drop k) s
        rw [hdrop, evalLinearized]
        -- Both sides: (r.signal s).bind (fun sig => ...)
        congr 1; funext sig
        -- Equate the transition arguments using hempty
        exact congrArg (evalLinearized G σ (G.rounds.drop (k + 1)))
          (congrArg (r.transition s) (hempty _ _))
    case h_2 hr =>
      -- G.rounds[k]? = none: step is identity
      simp [PMF.pure_bind]
  | playerTurn k s sig p accActs =>
    -- Step resolves player p; evalFromCfg resolves p onward
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      simp only [advancePlayerTurn]
      rw [extractPlayerAction_lift σ k s sig p accActs r hr]
      split
      case isTrue hp1 =>
        -- p.val + 1 < n: advance to next player
        simp only [PMF.pure_bind, evalFromCfg, hr]
        congr 1
        -- resolveActions from p with updated accActs = resolveActions from p with original
        conv_rhs => rw [show p.val = p.val from rfl]; unfold resolveActions; rw [dif_pos p.isLt]
      case isFalse hp1 =>
        -- p is last player: advance → applyTransition
        have hresolve : resolveActions G σ r s sig p.val accActs =
            Function.update accActs p (σ p (r.view p s (sig p))) := by
          unfold resolveActions; rw [dif_pos p.isLt]
          have : ⟨p.val, p.isLt⟩ = p := Fin.ext rfl
          rw [this]; unfold resolveActions; rw [dif_neg hp1]
        -- LHS: PMF.pure (.applyTransition k s sig updatedActs).bind (evalFromCfg G σ)
        simp only [PMF.pure_bind, evalFromCfg, hr, hresolve]
    case h_2 hr =>
      simp [PMF.pure_bind, evalFromCfg, hr]
  | applyTransition k s sig accActs =>
    -- Step applies transition; evalFromCfg does the same thing
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      -- G.rounds[k]? = some r: transition fires
      split
      case h_1 _ hr2 =>
        -- G.rounds[k+1]? = some _: next round exists → signal (k+1)
        simp only [PMF.pure_bind]
        show evalFromCfg G σ (.signal (k + 1) (r.transition s accActs)) =
          evalFromCfg G σ (.applyTransition k s sig accActs)
        simp only [evalFromCfg, hr]
      case h_2 _ hr2 =>
        -- G.rounds[k+1]? = none: terminal
        simp only [PMF.pure_bind]
        show evalFromCfg G σ (.terminal (r.transition s accActs)) =
          evalFromCfg G σ (.applyTransition k s sig accActs)
        simp only [evalFromCfg, hr]
        have hdrop2 : G.rounds.drop (k + 1) = [] :=
          List.drop_eq_nil_of_le (by
            by_contra h; push_neg at h
            rw [List.getElem?_eq_getElem h] at hr2; exact absurd hr2 (by simp))
        rw [hdrop2, evalLinearized]
    case h_2 hr =>
      simp [PMF.pure_bind, evalFromCfg, hr]

/-- **Telescoping**: running the linearized model for `k` steps and composing
with `evalFromCfg` on the last state equals `evalFromCfg` at the initial config,
which is `Protocol.eval`.

Proof idea: by induction on `k`, using `stepPMF_bind_evalFromCfg` at each step
to show that one step composed with `evalFromCfg` telescopes back to `evalFromCfg`
on the previous last state. The base case is `evalFromCfg_init`. -/
private theorem lastState_snoc (ss : List (LinConfig G)) (t : LinConfig G) :
    (compiledLinObs G).lastState (ss ++ [t]) = t := by
  simp [ObsModelCore.lastState, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil t [])]

theorem runDistPure_bind_evalFromCfg [Fintype A]
    (σ : PureProfile n V A) (k : Nat) :
    ((compiledLinObs G).runDistPure k (liftPureProfile σ)).bind
        (fun ss => evalFromCfg G σ ((compiledLinObs G).lastState ss)) =
      G.eval σ := by
  induction k with
  | zero =>
    change (PMF.pure [(compiledLinObs G).init]).bind _ = _
    simp only [PMF.pure_bind, ObsModelCore.lastState, List.getLast?_singleton, Option.getD_some]
    exact evalFromCfg_init G σ
  | succ k ih =>
    change ((ObsModelCore.runDistPure (compiledLinObs G) k (liftPureProfile σ)).bind
      (fun ss => Math.ProbabilityMassFunction.pushforward
        ((compiledLinObs G).pureStep (liftPureProfile σ) ss)
        (fun t => ss ++ [t]))).bind
      (fun ss => evalFromCfg G σ ((compiledLinObs G).lastState ss)) = _
    simp only [PMF.bind_bind, Math.ProbabilityMassFunction.pushforward, PMF.pure_bind,
      lastState_snoc]
    simp_rw [pureStep_compiledLin_eq, stepPMF_bind_evalFromCfg]
    exact ih

/-- A `LinConfig` is "done" when `evalFromCfg` reduces to `PMF.pure ∘ state`:
terminal configs, and non-terminal configs past all rounds. -/
def LinConfig.isDone (G : Protocol n S V A Sig) : LinConfig G → Prop
  | .terminal _ => True
  | .signal k _ => G.rounds[k]? = none
  | .playerTurn k _ _ _ _ => G.rounds[k]? = none
  | .applyTransition k _ _ _ => G.rounds[k]? = none

/-- Combined round+player phase measure. Increases by ≥1 at each non-done step.
Terminal configs get maximum phase so that monotonicity holds universally. -/
def LinConfig.phase (G : Protocol n S V A Sig) : LinConfig G → Nat
  | .signal k _ => k * (n + 2)
  | .playerTurn k _ _ p _ => k * (n + 2) + p.val + 1
  | .applyTransition k _ _ _ => k * (n + 2) + n + 1
  | .terminal _ => G.rounds.length * (n + 2)

private theorem evalFromCfg_of_isDone (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (cfg : LinConfig G)
    (hd : cfg.isDone G) :
    evalFromCfg G σ cfg = PMF.pure cfg.state := by
  cases cfg with
  | terminal s => rfl
  | signal k s =>
    change evalLinearized G σ (G.rounds.drop k) s = PMF.pure s
    have hdr : G.rounds.drop k = [] := by
      apply List.drop_eq_nil_of_le
      by_contra h; push_neg at h
      have : G.rounds[k]? = some G.rounds[k] := List.getElem?_eq_getElem h
      simp [LinConfig.isDone, this] at hd
    rw [hdr, evalLinearized]
  | playerTurn k s sig p accActs =>
    change (match G.rounds[k]? with | some r => _ | none => PMF.pure s) = PMF.pure s
    have hd' : G.rounds[k]? = none := hd
    rw [hd']
  | applyTransition k s sig accActs =>
    change (match G.rounds[k]? with | some r => _ | none => PMF.pure s) = PMF.pure s
    have hd' : G.rounds[k]? = none := hd
    rw [hd']

omit [DecidableEq (Fin n)] in
private theorem isDone_of_phase_ge (G : Protocol n S V A Sig)
    (cfg : LinConfig G) (h : cfg.phase G ≥ G.rounds.length * (n + 2)) :
    cfg.isDone G := by
  cases cfg with
  | terminal _ => trivial
  | signal k s =>
    simp only [LinConfig.phase] at h
    have hk : k ≥ G.rounds.length := Nat.le_of_mul_le_mul_right h (by omega)
    simp only [LinConfig.isDone]
    exact List.getElem?_eq_none (by omega)
  | playerTurn k s sig p accActs =>
    simp only [LinConfig.phase] at h
    have hk : k ≥ G.rounds.length := by
      by_contra hlt; push_neg at hlt
      have : k * (n + 2) + p.val + 1 ≤ k * (n + 2) + n + 1 := by omega
      have : k * (n + 2) + n + 1 < G.rounds.length * (n + 2) := by nlinarith
      omega
    simp only [LinConfig.isDone]
    exact List.getElem?_eq_none (by omega)
  | applyTransition k s sig accActs =>
    simp only [LinConfig.phase] at h
    have hk : k ≥ G.rounds.length := by
      by_contra hlt; push_neg at hlt
      have : k * (n + 2) + n + 1 < G.rounds.length * (n + 2) := by nlinarith
      omega
    simp only [LinConfig.isDone]
    exact List.getElem?_eq_none (by omega)

omit [DecidableEq (Fin n)] in
private theorem phase_init_le (G : Protocol n S V A Sig) :
    (linInitialConfig G).phase G ≤ G.rounds.length * (n + 2) := by
  simp only [linInitialConfig]
  split <;> simp [LinConfig.phase]

/-- At done configs, any successor is also done and has the same state. -/
theorem isDone_step_of_isDone (G : Protocol n S V A Sig)
    (cfg : LinConfig G)
    (acts : (i : Fin n) → LinAct (RoundView G) A (linObserve G i cfg))
    (hd : cfg.isDone G) (t : LinConfig G)
    (ht : t ∈ (linConfigStepPMF G cfg acts).support) :
    t.isDone G ∧ t.state = cfg.state := by
  rw [PMF.mem_support_iff] at ht
  cases cfg with
  | terminal s =>
    have ht' := (pure_ne_zero_iff' _ t).mp (by rwa [linConfigStepPMF] at ht)
    subst ht'; exact ⟨trivial, rfl⟩
  | signal k s =>
    simp only [linConfigStepPMF] at ht; split at ht
    · rename_i r hr; exact absurd hr (by change G.rounds[k]? = none at hd; simp [hd])
    · rw [pure_ne_zero_iff'] at ht; subst ht; exact ⟨hd, rfl⟩
  | playerTurn k s sig p accActs =>
    simp only [linConfigStepPMF] at ht; split at ht
    · rename_i r hr; exact absurd hr (by change G.rounds[k]? = none at hd; simp [hd])
    · rw [pure_ne_zero_iff'] at ht; subst ht; exact ⟨hd, rfl⟩
  | applyTransition k s sig accActs =>
    simp only [linConfigStepPMF] at ht; split at ht
    · rename_i r hr; exact absurd hr (by change G.rounds[k]? = none at hd; simp [hd])
    · rw [pure_ne_zero_iff'] at ht; subst ht; exact ⟨trivial, rfl⟩

/-- At non-done configs, every successor has phase exactly `cfg.phase + 1`. -/
theorem phase_step_progress (G : Protocol n S V A Sig)
    (cfg : LinConfig G)
    (acts : (i : Fin n) → LinAct (RoundView G) A (linObserve G i cfg))
    (hnd : ¬ cfg.isDone G) (t : LinConfig G)
    (ht : t ∈ (linConfigStepPMF G cfg acts).support) :
    t.phase G = cfg.phase G + 1 := by
  rw [PMF.mem_support_iff] at ht
  cases cfg with
  | terminal s => exact absurd trivial hnd
  | signal k s =>
    simp only [linConfigStepPMF] at ht
    -- Split on match G.rounds[k]?
    split at ht
    · -- some r branch: split on if 0 < n
      rename_i r hr
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      split at ht
      · -- 0 < n: (r.signal s).map (fun sig => .playerTurn k s sig ⟨0, _⟩ _)
        rename_i hn
        obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ t).mp
          ((PMF.mem_support_iff _ t).mpr ht)
        simp [LinConfig.phase]
      · -- ¬(0 < n): map to .applyTransition
        rename_i hn
        have h0 : n = 0 := by omega
        obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ t).mp
          ((PMF.mem_support_iff _ t).mpr ht)
        simp only [LinConfig.phase]; subst h0; omega
    · -- none branch: contradicts ¬isDone
      exact absurd (by assumption : G.rounds[k]? = none) hnd
  | playerTurn k s sig p accActs =>
    simp only [linConfigStepPMF] at ht
    split at ht
    · -- some r branch
      rename_i r hr
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      simp only [advancePlayerTurn] at ht
      have hpn : p.val < n := p.isLt
      split at ht
      · rename_i hp1
        obtain rfl := (pure_ne_zero_iff' _ t).mp ht
        simp only [LinConfig.phase]; omega
      · rename_i hp1
        obtain rfl := (pure_ne_zero_iff' _ t).mp ht
        simp only [LinConfig.phase]
        nlinarith [show p.val + 1 = n by omega]
    · -- none branch: contradicts ¬isDone
      exact absurd (by assumption : G.rounds[k]? = none) hnd
  | applyTransition k s sig accActs =>
    simp only [linConfigStepPMF] at ht
    split at ht
    · -- some r branch: transition fires
      rename_i r hr
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      split at ht
      · -- G.rounds[k+1]? = some _: signal (k+1)
        obtain rfl := (pure_ne_zero_iff' _ t).mp ht
        simp only [LinConfig.phase]; nlinarith
      · -- G.rounds[k+1]? = none: terminal
        rename_i hknone
        have hklen : G.rounds.length = k + 1 := by
          have hge : G.rounds.length ≤ k + 1 := by
            simp only [List.getElem?_eq_none_iff] at hknone; exact hknone
          omega
        obtain rfl := (pure_ne_zero_iff' _ t).mp ht
        simp only [LinConfig.phase]; nlinarith
    · -- none branch: contradicts ¬isDone
      exact absurd (by assumption : G.rounds[k]? = none) hnd

private theorem PMF.bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ x ∈ p.support, f x = g x) : p.bind f = p.bind g := by
  ext b; simp only [PMF.bind_apply]
  congr 1; ext a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]

/-- After `k ≥ rounds.length * (n+1)` steps, all reachable last states are done. -/
private theorem isDone_of_reachable [Fintype A]
    (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (k : Nat) (ss : List (LinConfig G))
    (hss : ss ∈ ((compiledLinObs G).runDistPure k (liftPureProfile σ)).support) :
    ((compiledLinObs G).lastState ss).isDone G ∨
    ((compiledLinObs G).lastState ss).phase G ≥ k := by
  rw [PMF.mem_support_iff] at hss
  induction k generalizing ss with
  | zero => right; omega
  | succ k ih =>
    -- Unfold runDistPure (k+1) using support membership
    change _ at hss
    rw [show (compiledLinObs G).runDistPure (k + 1) (liftPureProfile σ) =
      ((compiledLinObs G).runDistPure k (liftPureProfile σ)).bind
        (fun ss' => Math.ProbabilityMassFunction.pushforward
          ((compiledLinObs G).pureStep (liftPureProfile σ) ss')
          (fun t => ss' ++ [t])) from rfl] at hss
    have hsupp := (PMF.mem_support_iff _ _).mpr hss
    rw [PMF.mem_support_bind_iff] at hsupp
    obtain ⟨ss', hss'_supp, ht_supp⟩ := hsupp
    -- pushforward: ss = ss' ++ [t] for some t in pureStep support
    rw [show Math.ProbabilityMassFunction.pushforward
        ((compiledLinObs G).pureStep (liftPureProfile σ) ss')
        (fun t => ss' ++ [t]) =
      ((compiledLinObs G).pureStep (liftPureProfile σ) ss').map
        (fun t => ss' ++ [t]) from rfl] at ht_supp
    rw [PMF.mem_support_map_iff] at ht_supp
    obtain ⟨t, ht_in_step, rfl⟩ := ht_supp
    rw [lastState_snoc]
    -- IH on ss'
    have ih_ss' := ih ss' ((PMF.mem_support_iff _ _).mp hss'_supp)
    -- t is in support of pureStep at ss'
    rw [pureStep_compiledLin_eq] at ht_in_step
    set cfg := (compiledLinObs G).lastState ss' with cfg_def
    set acts := (fun i => (liftPureProfile (G := G) σ) i (linObserve G i cfg))
    -- Case split on whether cfg is done
    by_cases hd : cfg.isDone G
    · -- cfg is done: successor is also done
      left
      exact (isDone_step_of_isDone G cfg acts hd t ht_in_step).1
    · -- Not done: phase increases
      right
      have hprog := phase_step_progress G cfg acts hd t ht_in_step
      rcases ih_ss' with hd' | hph
      · exact absurd hd' hd
      · omega

/-- **Adequacy (pure profiles)**: running the linearized compiled model with
`liftPureProfile σ` for enough steps, and extracting the terminal state, gives
the same distribution as `Protocol.eval G σ`. -/
theorem runDistPure_eq_eval (G : Protocol n S V A Sig) [Fintype A]
    (σ : PureProfile n V A) (k : Nat) (hk : k ≥ G.rounds.length * (n + 2)) :
    ((compiledLinObs G).runDistPure k (liftPureProfile σ)).bind
        (fun ss => PMF.pure ((compiledLinObs G).lastState ss).state) =
      G.eval σ := by
  have htele := runDistPure_bind_evalFromCfg (G := G) σ k
  rw [← htele]
  exact PMF.bind_congr_support _ _ _ fun ss hss => by
    have hdr := isDone_of_reachable G σ k ss hss
    rcases hdr with hd | hph
    · exact (evalFromCfg_of_isDone G σ _ hd).symm
    · exact (evalFromCfg_of_isDone G σ _ (isDone_of_phase_ge G _ (by omega))).symm

end Adequacy

-- ============================================================================
-- Behavioral adequacy: linearized execution matches Protocol.evalMixed
-- ============================================================================

section BehavioralAdequacy

variable {G : Protocol n S V A Sig} [DecidableEq (Fin n)] [Fintype (Option A)]

/-- Resolve players `pVal, pVal+1, ..., n-1` by sampling from behavioral
strategies, accumulating actions into `accActs`. -/
noncomputable def resolveActionsMixed
    (σ : BehavioralProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) (pVal : Nat) (accActs : Fin n → Option A) :
    PMF (Fin n → Option A) :=
  if hp : pVal < n then
    let p : Fin n := ⟨pVal, hp⟩
    (σ p (r.view p s (sig p))).bind fun a =>
      resolveActionsMixed σ r s sig (pVal + 1) (Function.update accActs p a)
  else
    PMF.pure accActs
  termination_by (n - pVal)

private theorem resolveActionsMixed_gen [Fintype (Fin n)]
    (σ : BehavioralProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) (pVal : Nat) (accActs : Fin n → Option A) :
    resolveActionsMixed σ r s sig pVal accActs =
      Math.PMFProduct.pmfPi (fun i : Fin n =>
        if i.val < pVal then PMF.pure (accActs i)
        else σ i (r.view i s (sig i))) := by
  suffices h : ∀ m, m = n - pVal → resolveActionsMixed σ r s sig pVal accActs =
      Math.PMFProduct.pmfPi (fun i : Fin n =>
        if i.val < pVal then PMF.pure (accActs i)
        else σ i (r.view i s (sig i))) from h _ rfl
  intro m
  induction m generalizing pVal accActs with
  | zero =>
    intro hm
    have hp : ¬ pVal < n := by omega
    rw [resolveActionsMixed, dif_neg hp]
    have : ∀ (i : Fin n), i.val < pVal := fun i => by omega
    simp only [this, ite_true]
    exact (Math.PMFProduct.pmfPi_pure accActs).symm
  | succ m ih =>
    intro hm
    have hp : pVal < n := by omega
    rw [resolveActionsMixed, dif_pos hp]
    let q : Fin n := ⟨pVal, hp⟩
    -- Apply IH to each branch of the bind
    change (σ q (r.view q s (sig q))).bind (fun a =>
      resolveActionsMixed σ r s sig (pVal + 1) (Function.update accActs q a)) = _
    have hbind : ∀ a, resolveActionsMixed σ r s sig (pVal + 1) (Function.update accActs q a) =
        Math.PMFProduct.pmfPi (fun i : Fin n =>
          if i.val < pVal + 1 then PMF.pure (Function.update accActs q a i)
          else σ i (r.view i s (sig i))) := fun a => ih (pVal + 1) _ (by omega)
    simp_rw [hbind]
    -- Define the family for the RHS
    let σ' := fun i : Fin n => if i.val < pVal then PMF.pure (accActs i)
        else σ i (r.view i s (sig i))
    -- Show the families agree
    suffices hfam : ∀ a,
        Math.PMFProduct.pmfPi (fun i : Fin n =>
          if i.val < pVal + 1 then PMF.pure (Function.update accActs q a i)
          else σ i (r.view i s (sig i))) =
        Math.PMFProduct.pmfPi (Function.update σ' q (PMF.pure a)) by
      simp_rw [hfam]
      have hσ'q : σ' q = σ q (r.view q s (sig q)) := by
        change (if pVal < pVal then _ else _) = _
        simp
      rw [show Math.PMFProduct.pmfPi σ' =
          Math.PMFProduct.pmfPi (Function.update σ' q (σ q (r.view q s (sig q)))) from by
        rw [Function.update_eq_self_iff.mpr hσ'q.symm]]
      rw [Math.PMFProduct.pmfPi_update_bind]
    intro a; congr 1; funext i
    by_cases hi : i = q
    · subst hi
      simp only [Function.update_self, σ']
      -- goal: (if ↑q < pVal + 1 then PMF.pure a else ...) = PMF.pure a
      have : (q : Fin n).val < pVal + 1 := show pVal < pVal + 1 from by omega
      rw [if_pos this]
    · simp only [Function.update_of_ne hi, σ']
      -- goal: (if ↑i < pVal + 1 then ... else ...) = (if ↑i < pVal then ... else ...)
      have hne : i.val ≠ pVal := fun h => hi (Fin.ext h)
      congr 1; ext; constructor <;> intro h <;> omega

/-- Resolving from player 0 with default actions equals the joint behavioral
sampling `pmfPi (fun i => σ i (r.view i s (sig i)))`. -/
theorem resolveActionsMixed_eq_pmfPi [Fintype (Fin n)]
    (σ : BehavioralProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) :
    resolveActionsMixed σ r s sig 0 (fun _ => none) =
      Math.PMFProduct.pmfPi (fun i => σ i (r.view i s (sig i))) :=
  resolveActionsMixed_gen σ r s sig 0 _

/-- Evaluate from a `LinConfig` using behavioral strategies. Like `evalFromCfg`
but samples actions from behavioral distributions rather than applying pure
strategies deterministically. -/
noncomputable def evalFromCfgMixed
    (G : Protocol n S V A Sig) (σ : BehavioralProfile n V A) : LinConfig G → PMF S
  | .terminal s => PMF.pure s
  | .signal k s => evalRoundsMixed (G.rounds.drop k) σ s
  | .playerTurn k s sig p accActs =>
      match G.rounds[k]? with
      | some r =>
        (resolveActionsMixed σ r s sig p.val accActs).bind fun fullActs =>
          let next := r.transition s fullActs
          evalRoundsMixed (G.rounds.drop (k + 1)) σ next
      | none => PMF.pure s
  | .applyTransition k s _sig accActs =>
      match G.rounds[k]? with
      | some r =>
        let next := r.transition s accActs
        evalRoundsMixed (G.rounds.drop (k + 1)) σ next
      | none => PMF.pure s

/-- `evalFromCfgMixed` at the initial configuration equals `Protocol.evalMixed`. -/
theorem evalFromCfgMixed_init (G : Protocol n S V A Sig)
    (σ : BehavioralProfile n V A) :
    evalFromCfgMixed G σ (linInitialConfig G) = G.evalMixed σ := by
  simp only [linInitialConfig]
  split <;> simp only [evalFromCfgMixed]
  · -- G.rounds[0]? = none → rounds is empty
    rename_i h
    have hnil : G.rounds = [] := by
      match hr : G.rounds with
      | [] => rfl
      | _ :: _ => simp [hr] at h
    simp [Protocol.evalMixed, evalRoundsMixed, hnil]
  · -- G.rounds[0]? ≠ none → signal case
    rw [List.drop_zero]
    rfl

/-- At done configs, `evalFromCfgMixed` reduces to `PMF.pure cfg.state`. -/
private theorem evalFromCfgMixed_of_isDone (G : Protocol n S V A Sig)
    (σ : BehavioralProfile n V A) (cfg : LinConfig G)
    (hd : cfg.isDone G) :
    evalFromCfgMixed G σ cfg = PMF.pure cfg.state := by
  cases cfg with
  | terminal s => rfl
  | signal k s =>
    change evalRoundsMixed (G.rounds.drop k) σ s = PMF.pure s
    have hdr : G.rounds.drop k = [] := by
      apply List.drop_eq_nil_of_le
      by_contra h; push_neg at h
      have : G.rounds[k]? = some G.rounds[k] := List.getElem?_eq_getElem h
      simp [LinConfig.isDone, this] at hd
    rw [hdr]; rfl
  | playerTurn k s sig p accActs =>
    change (match G.rounds[k]? with | some r => _ | none => PMF.pure s) = PMF.pure s
    have hd' : G.rounds[k]? = none := hd
    rw [hd']
  | applyTransition k s sig accActs =>
    change (match G.rounds[k]? with | some r => _ | none => PMF.pure s) = PMF.pure s
    have hd' : G.rounds[k]? = none := hd
    rw [hd']

variable [Fintype (Fin n)] [Fintype A]

omit [Fintype (Option A)] in
/-- Any config reachable via `stepDist` is in the support of `linConfigStepPMF`
for some action choice. -/
private theorem stepDist_support_subset_step_support
    {β : ObsModelCore.BehavioralProfile (compiledLinObs G)}
    {ss : List (LinConfig G)} {t : LinConfig G}
    (ht : t ∈ ((compiledLinObs G).stepDist β ss).support) :
    ∃ acts, t ∈ (linConfigStepPMF G ((compiledLinObs G).lastState ss) acts).support := by
  simp only [ObsModelCore.stepDist, PMF.mem_support_bind_iff] at ht
  obtain ⟨a, _, ht'⟩ := ht
  exact ⟨(compiledLinObs G).castJointAction ss a, ht'⟩

omit [Fintype (Option A)] in
/-- For large enough k, all configs reachable by `runDist k β` are done. -/
private theorem isDone_of_reachable_behavioral
    {β : ObsModelCore.BehavioralProfile (compiledLinObs G)}
    (k : Nat) (ss : List (LinConfig G))
    (hss : ((compiledLinObs G).runDist k β) ss ≠ 0) :
    ((compiledLinObs G).lastState ss).isDone G ∨
    ((compiledLinObs G).lastState ss).phase G ≥ k := by
  induction k generalizing ss with
  | zero => right; omega
  | succ k ih =>
    change _ at hss
    rw [show (compiledLinObs G).runDist (k + 1) β =
      ((compiledLinObs G).runDist k β).bind
        (fun ss' => Math.ProbabilityMassFunction.pushforward
          ((compiledLinObs G).stepDist β ss')
          (fun t => ss' ++ [t])) from rfl] at hss
    have hsupp := (PMF.mem_support_iff _ _).mpr hss
    rw [PMF.mem_support_bind_iff] at hsupp
    obtain ⟨ss', hss'_supp, ht_supp⟩ := hsupp
    rw [show Math.ProbabilityMassFunction.pushforward
        ((compiledLinObs G).stepDist β ss')
        (fun t => ss' ++ [t]) =
      ((compiledLinObs G).stepDist β ss').map
        (fun t => ss' ++ [t]) from rfl] at ht_supp
    rw [PMF.mem_support_map_iff] at ht_supp
    obtain ⟨t, ht_in_step, rfl⟩ := ht_supp
    rw [lastState_snoc]
    have ih_ss' := ih ss' ((PMF.mem_support_iff _ _).mp hss'_supp)
    obtain ⟨acts', ht_acts⟩ := stepDist_support_subset_step_support ht_in_step
    by_cases hd : ((compiledLinObs G).lastState ss').isDone G
    · left; exact (isDone_step_of_isDone G _ acts' hd t ht_acts).1
    · right
      have hprog := phase_step_progress G _ acts' hd t ht_acts
      rcases ih_ss' with hd' | hph
      · exact absurd hd' hd
      · omega

private theorem stepDist_liftBehavioral_bind_evalFromCfgMixed
    (σ : BehavioralProfile n V A) (ss : List (LinConfig G)) :
    ((compiledLinObs G).stepDist (liftBehavioralProfile σ) ss).bind
        (evalFromCfgMixed G σ) =
      evalFromCfgMixed G σ ((compiledLinObs G).lastState ss) := by
  -- Unfold stepDist and merge binds.
  simp only [ObsModelCore.stepDist, ObsModelCore.jointActionDist]
  rw [PMF.bind_bind]
  -- Relate projectStates to linObserve at lastState (identity info states).
  have hps : ∀ i, (compiledLinObs G).projectStates i ss =
      linObserve G i ((compiledLinObs G).lastState ss) := fun i => by
    have h := ObsModelCore.currentObs_projectStates (compiledLinObs G) i ss
    simp only [ObsModelCore.currentObs, compileObsCoreModelLin] at h; exact h
  -- suffices: prove the result by cases on the config type of lastState ss.
  -- We use a helper that takes cfg explicitly, avoiding castJointAction issues.
  suffices helper : ∀ (cfg : LinConfig G)
      (obs : Fin n → Option (RoundView G))
      (hobs : ∀ i, obs i = linObserve G i cfg),
      ((Math.PMFProduct.pmfPi (fun i =>
          liftBehavioralStrategy (G := G) (σ i) (obs i))).bind
        (fun a => (linConfigStepPMF G cfg
          (fun i => cast (congrArg (LinAct (RoundView G) A) (hobs i)) (a i))).bind
          (evalFromCfgMixed G σ))) =
      evalFromCfgMixed G σ cfg by
    convert helper ((compiledLinObs G).lastState ss)
      (fun i => (compiledLinObs G).projectStates i ss) hps using 2
    rename_i a
    funext j; congr 1; congr 1
    funext i
    -- Both sides transport j i along propositionally equal proofs.
    -- castJointAction uses currentObs_projectStates, the other uses hps.
    simp only [ObsModelCore.castJointAction, compileObsCoreModelLin]
    simp [eqRec_eq_cast]
    rfl
  -- Now prove the helper by cases on cfg.
  intro cfg obs hobs
  cases cfg with
  | terminal s =>
    -- All obs are none, step is PMF.pure (terminal s)
    have hall : ∀ i, obs i = none := fun i => by simp [hobs, linObserve]
    simp only [linConfigStepPMF, PMF.pure_bind, evalFromCfgMixed]
    simp [PMF.bind_const]
  | signal k s =>
    -- All obs are none for signal configs
    have hall : ∀ i, obs i = none := fun i => by simp [hobs, linObserve]
    -- linConfigStepPMF at signal doesn't use the action tuple.
    -- Show the function is constant, then use PMF.bind_const.
    have default_a : (i : Fin n) → LinAct (RoundView G) A (obs i) :=
      fun i => (hall i).symm ▸ PUnit.unit
    have hconst : ∀ (a : (i : Fin n) → LinAct (RoundView G) A (obs i)),
        (linConfigStepPMF G (.signal k s)
          (fun i => cast (congrArg _ (hobs i)) (a i))).bind
          (evalFromCfgMixed G σ) =
        (linConfigStepPMF G (.signal k s)
          (fun i => cast (congrArg _ (hobs i)) (default_a i))).bind
          (evalFromCfgMixed G σ) := by
      intro a; congr 1
    simp_rw [hconst]; rw [PMF.bind_const]
    -- Now: step(any_acts).bind(eval) = eval(signal k s)
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      have hdrop : G.rounds.drop k = r :: G.rounds.drop (k + 1) := by
        rw [← List.cons_getElem_drop_succ (h := hk)]
        congr 1; exact (List.getElem_of_getElem? hr).choose_spec
      split
      case isTrue hn =>
        rw [PMF.bind_map]
        simp only [Function.comp_def, evalFromCfgMixed, hr, hdrop, evalRoundsMixed_cons,
          Round.evalMixed, PMF.bind_bind]
        congr 1; funext sig'
        conv_rhs => rw [PMF.bind_map]; simp only [Function.comp_def]
        rw [resolveActionsMixed_eq_pmfPi]; convert rfl using 3
      case isFalse hn =>
        rw [PMF.bind_map]
        simp only [Function.comp_def, evalFromCfgMixed, hr, hdrop, evalRoundsMixed_cons,
          Round.evalMixed, PMF.bind_bind]
        congr 1; funext sig'
        have hn0 : n = 0 := by omega
        subst hn0
        have : ∀ f : Fin 0 → Option A, r.transition s f = r.transition s (fun _ => none) := by
          intro f; congr 1; funext i; exact Fin.elim0 i
        simp_rw [this]
        have hmc : (fun acts : Fin 0 → Option A => r.transition s fun x => none) =
            Function.const _ (r.transition s fun x => none) := funext fun _ => rfl
        rw [hmc, PMF.map_const, PMF.pure_bind]
    case h_2 hr =>
      simp [PMF.pure_bind, evalFromCfgMixed]
  | playerTurn k s sig p accActs =>
    simp only [linConfigStepPMF]
    split
    case h_2 hr =>
      -- G.rounds[k]? = none: step is pure, all obs are none
      have hlen : G.rounds.length ≤ k := by
        by_contra h; push_neg at h; rw [List.getElem?_eq_getElem h] at hr; exact absurd hr (by simp)
      have hall : ∀ i, obs i = none := fun i => by
        rw [hobs]; simp [linObserve, show ¬(k < G.rounds.length) from by omega]
      simp only [PMF.pure_bind, evalFromCfgMixed, hr]
      simp only [PMF.bind_const]
    case h_1 r hr =>
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      -- Observations: player p sees some, others see none
      have hobs_p : obs p = some (⟨k, hk⟩, r.view p s (sig p)) := by
        rw [hobs]; simp [linObserve, hk, (List.getElem_of_getElem? hr).choose_spec]
      have hobs_ne : ∀ i, i ≠ p → obs i = none := fun i hi => by
        rw [hobs]; simp [linObserve, hi]
      -- Unfold advancePlayerTurn and evalFromCfgMixed on the RHS
      simp only [advancePlayerTurn, evalFromCfgMixed, hr]
      -- Unfold resolveActionsMixed one step
      rw [resolveActionsMixed, dif_pos p.isLt]
      simp only [PMF.bind_bind]
      -- The continuation only depends on extractPlayerAction, which only uses a p.
      -- We'll show extractPlayerAction gives cast(a p) = the Option A value of a p.
      -- Then factor the pmfPi to extract player p's marginal.
      -- Step 1: Simplify the bind. Push pure_bind inside the if.
      have hbind_eq :
          ∀ a : (i : Fin n) → LinAct (RoundView G) A (obs i),
          ((if h : ↑p + 1 < n then
              PMF.pure (LinConfig.playerTurn k s sig ⟨↑p + 1, h⟩
                (Function.update accActs p
                  (extractPlayerAction G k s sig p accActs
                    fun i => cast (congrArg _ (hobs i)) (a i))))
            else
              PMF.pure (LinConfig.applyTransition k s sig
                (Function.update accActs p
                  (extractPlayerAction G k s sig p accActs
                    fun i => cast (congrArg _ (hobs i)) (a i))))).bind
            (evalFromCfgMixed G σ)) =
          (resolveActionsMixed σ r s sig (↑p + 1)
            (Function.update accActs p
              (extractPlayerAction G k s sig p accActs
                fun i => cast (congrArg _ (hobs i)) (a i)))).bind
            fun fullActs =>
              evalRoundsMixed (G.rounds.drop (k + 1)) σ
                (r.transition s fullActs) := by
        intro a
        split
        case isTrue hp1 =>
          rw [PMF.pure_bind]
          simp only [evalFromCfgMixed, hr]
        case isFalse hp1 =>
          rw [PMF.pure_bind]
          simp only [evalFromCfgMixed, hr]
          rw [resolveActionsMixed, dif_neg (by omega)]
          simp [PMF.pure_bind]
      simp_rw [hbind_eq]
      -- Step 2: extractPlayerAction with cast gives cast(a p).
      -- extractPlayerAction uses cast based on linObserve.
      -- Net effect: extractPlayerAction = a p (modulo cast).
      have hextract :
          ∀ a : (i : Fin n) → LinAct (RoundView G) A (obs i),
          extractPlayerAction G k s sig p accActs
            (fun i => cast (congrArg _ (hobs i)) (a i)) =
          cast (congrArg _ hobs_p) (a p) := by
        intro a
        unfold extractPlayerAction
        rw [dif_pos hk]
        simp only [cast_cast]
        rfl
      simp_rw [hextract]
      -- Goal: pmfPi(lift).bind(fun a => g(cast(a p))) = (σ p view).bind(fun ap => g ap)
      -- The cast transports LinAct(obs p) → LinAct(some(k_fin, view)) = Option A.
      -- We prove the two sides are equal using pmfPi_bind_eval after
      -- eliminating the cast via congrArg on the continuation.
      -- First, show the cast is identity by changing it to an Eq.rec and using
      -- proof that the two types are equal via hobs_p.
      -- pmfPi_bind_eval says: pmfPi(σ).bind(fun s => f(s j)) = (σ j).bind f
      -- Our continuation is: fun a => g(cast ⋯ (a p))
      -- = fun a => (fun ap => g(cast ⋯ ap)) (a p)
      -- = fun a => f(a p) where f = fun ap => g(cast ⋯ ap)
      -- So pmfPi_bind_eval gives:
      -- (liftBehavioralStrategy (σ p) (obs p)).bind(fun ap => g(cast ⋯ ap))
      -- We need this to equal (σ p view).bind g.
      -- Key: cast ⋯ is a function LinAct(obs p) → Option A, and
      -- liftBehavioralStrategy (σ p) (obs p) : PMF (LinAct(obs p)).
      -- We use the fact that for any h : α = β,
      -- (cast (show PMF α = PMF β from congrArg PMF h) d).bind f = d.bind (f ∘ cast h)
      -- And liftBehavioralStrategy (σ p) (obs p) = cast ⋯ (σ p view).
      -- Then: (cast ⋯ (σ p view)).bind(f ∘ cast ⋯) = (σ p view).bind f.
      -- Actually, let's use a simpler approach.
      -- Directly show: ∀ (h : obs p = some(k, v)),
      -- Factor the pmfPi to extract player p's marginal via pmfPi_bind_eval.
      have heval := Math.PMFProduct.pmfPi_bind_eval
        (fun i => liftBehavioralStrategy (G := G) (σ i) (obs i)) p
        (fun (ap : LinAct (RoundView G) A (obs p)) =>
          (resolveActionsMixed σ r s sig (↑p + 1)
            (Function.update accActs p (cast (congrArg (LinAct (RoundView G) A) hobs_p) ap))).bind
            fun fullActs => evalRoundsMixed (G.rounds.drop (k + 1)) σ (r.transition s fullActs))
      refine heval.trans ?_; clear heval
      -- Goal: (liftBehav(σ p)(obs p)).bind(fun ap => g(cast ap)) = (σ p view).bind g
      -- Generalize obs p to a free variable so we can subst.
      set op := obs p with hop_def
      rw [hobs_p] at hop_def
      -- Now op = some(⟨k,hk⟩, r.view p s (sig p)) and we have hobs_p : op = some(...)
      -- But op appears in the types. We need to rewrite using hobs_p.
      -- Use a general lemma: for h : α = β, cast h applied to bind gives the same.
      have key : ∀ (o : Option (RoundView G))
          (h : o = some (⟨k, hk⟩, r.view p s (sig p)))
          (g' : Option A → PMF S),
          (liftBehavioralStrategy (G := G) (σ p) o).bind
            (fun ap => g' (cast (congrArg (LinAct (RoundView G) A) h) ap)) =
          (σ p (r.view p s (sig p))).bind g' := by
        intro o h g'; subst h; rfl
      convert key op hobs_p _ using 2
      ext ap; congr 2
  | applyTransition k s sig accActs =>
    -- All obs are none, step doesn't depend on actions
    have hall : ∀ i, obs i = none := fun i => by simp [hobs, linObserve]
    have default_a : (i : Fin n) → LinAct (RoundView G) A (obs i) :=
      fun i => (hall i).symm ▸ PUnit.unit
    have hconst : ∀ (a : (i : Fin n) → LinAct (RoundView G) A (obs i)),
        (linConfigStepPMF G (.applyTransition k s sig accActs)
          (fun i => cast (congrArg (LinAct (RoundView G) A) (hobs i)) (a i))).bind
          (evalFromCfgMixed G σ) =
        (linConfigStepPMF G (.applyTransition k s sig accActs)
          (fun i => cast (congrArg (LinAct (RoundView G) A) (hobs i)) (default_a i))).bind
          (evalFromCfgMixed G σ) := by
      intro a; congr 1
    simp_rw [hconst]; rw [PMF.bind_const]
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      split
      case h_1 _ hr2 =>
        simp only [PMF.pure_bind, evalFromCfgMixed, hr]
      case h_2 _ hr2 =>
        simp only [PMF.pure_bind, evalFromCfgMixed, hr]
        have hdrop2 : G.rounds.drop (k + 1) = [] :=
          List.drop_eq_nil_of_le (by
            by_contra h; push_neg at h
            rw [List.getElem?_eq_getElem h] at hr2; exact absurd hr2 (by simp))
        rw [hdrop2, evalRoundsMixed]; simp
    case h_2 hr =>
      simp [PMF.pure_bind, evalFromCfgMixed, hr]

/-- **Behavioral adequacy (telescoping)**: running the linearized model for `k`
steps under `liftBehavioralProfile σ` and composing with `evalFromCfgMixed`
equals `evalFromCfgMixed` at the initial configuration.

Uses `runDist_bind_interp` with the one-step simulation. -/
theorem runDist_liftBehavioral_bind_evalFromCfgMixed
    (σ : BehavioralProfile n V A) (k : Nat) :
    ((compiledLinObs G).runDist k (liftBehavioralProfile σ)).bind
        (fun ss => evalFromCfgMixed G σ ((compiledLinObs G).lastState ss)) =
      G.evalMixed σ := by
  have hstep := stepDist_liftBehavioral_bind_evalFromCfgMixed (G := G) σ
  have := ObsModelCore.runDist_bind_interp (compiledLinObs G)
    (evalFromCfgMixed G σ) (liftBehavioralProfile σ) hstep k
  rw [this]
  exact evalFromCfgMixed_init G σ

/-- **Behavioral adequacy (state extraction)**: running the linearized model
for enough steps and extracting the terminal state gives `Protocol.evalMixed`.

For large enough `k`, all reachable configs are done, so `evalFromCfgMixed`
reduces to `PMF.pure ∘ state`. -/
theorem runDist_liftBehavioral_extractState_eq_evalMixed
    (σ : BehavioralProfile n V A) (k : Nat) (hk : k ≥ G.rounds.length * (n + 2)) :
    ((compiledLinObs G).runDist k (liftBehavioralProfile σ)).bind
        (fun ss => PMF.pure ((compiledLinObs G).lastState ss).state) =
      G.evalMixed σ := by
  rw [← runDist_liftBehavioral_bind_evalFromCfgMixed (G := G) σ k]
  apply PMF.bind_congr_support
  intro ss hss
  have hdr := isDone_of_reachable_behavioral (G := G) k ss hss
  rcases hdr with hd | hph
  · exact (evalFromCfgMixed_of_isDone G σ _ hd).symm
  · exact (evalFromCfgMixed_of_isDone G σ _
      (isDone_of_phase_ge G _ (by omega))).symm

end BehavioralAdequacy

end GameTheory.Sequential
