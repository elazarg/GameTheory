import GameTheory.Languages.MAID.CompileObs
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Languages.MAID.Kuhn

Kuhn reduction lemmas for compiled MAIDs via `ObsModelCore`.

## Main results

- `kuhn_behavioral_to_mixed_compiledPR` : B→M direction via `compileObsCoreModelPR`,
  under `NoNontrivialInfoStateRepeat` (which holds for well-formed MAIDs)

## Architecture

**B→M** uses `compileObsCoreModelPR`, which compiles MAIDs with observation-dependent
action types (`CompiledMAIDAct`). Under perfect recall, at most one infoset per player
is active at any frontier step, and `NoNontrivialInfoStateRepeat` holds because each
decision node is processed exactly once in the frontier evaluation.

**M→B** requires linearized compilation (one node per step) to satisfy
`StepSupportFactorization`, since the simultaneous frontier compilation has
multiple players acting at once. This is planned but not yet implemented.
-/

namespace GameTheory.Languages.MAID

open _root_.MAID
open GameTheory.Theorems

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

section KuhnBToM

variable (S : Struct Player n) (sem : Sem S)

/-- The compiled PR ObsModelCore for a MAID. -/
noncomputable abbrev compiledPRObs (S : Struct Player n) (sem : Sem S) :=
  compileObsCoreModelPR S sem

/-- **Kuhn B→M for compiled MAIDs (PR model)**: behavioral strategies can be
realized as product mixed strategies, given the no-nontrivial-info-state-repeat
condition.

Under perfect recall, this condition holds automatically because each
decision node is processed exactly once in the frontier evaluation. -/
theorem kuhn_behavioral_to_mixed_compiledPR
    [∀ p, Fintype ((compiledPRObs S sem).InfoState p)]
    [∀ p, Fintype ((compiledPRObs S sem).LocalStrategy p)]
    (hNR : (compiledPRObs S sem).NoNontrivialInfoStateRepeat)
    (β : ObsModelCore.BehavioralProfile (compiledPRObs S sem)) (k : Nat) :
    (compiledPRObs S sem).runDist k β =
      ((compiledPRObs S sem).behavioralToMixedJoint β).bind
        ((compiledPRObs S sem).runDistPure k) :=
  ObsModelCore.kuhn_behavioral_to_mixed hNR β k

/-- If `frontierActiveInfoset` returns `some I`, then the decision node is enabled. -/
private theorem activeInfoset_mem_frontier
    (cfg : FrontierCfg S) (p : Player) (I : Infoset S p)
    (h : frontierActiveInfoset S cfg p = some I) :
    I.1.val ∈ frontier S cfg := by
  -- frontierActiveInfoset = (frontierInfosets S cfg p).head?
  -- head? = some I means I is the head of frontierInfosets
  simp only [frontierActiveInfoset] at h
  -- I is in frontierInfosets
  have hMem : I ∈ frontierInfosets S cfg p :=
    List.mem_of_head? h
  -- frontierInfosets is a filterMap over (frontier S cfg).toList
  simp only [frontierInfosets] at hMem
  rw [List.mem_filterMap] at hMem
  obtain ⟨nd, hnd_mem, hnd_val⟩ := hMem
  -- nd ∈ (frontier S cfg).toList, so nd ∈ frontier S cfg
  have hnd_frontier : nd ∈ frontier S cfg :=
    Finset.mem_toList.mp hnd_mem
  -- From the filterMap construction, I.1.val = nd
  -- The filterMap only produces some when kind nd = .decision p and nd ∈ frontier
  -- In that case it returns ⟨⟨nd, _⟩, _⟩, so I.1.val = nd
  -- Simplify the outer `if nd ∈ frontier` using hnd_frontier
  simp only [hnd_frontier, dite_true] at hnd_val
  -- Now hnd_val has `match S.kind nd with ...`; split on it
  revert hnd_val; intro hnd_val
  split at hnd_val
  · -- decision q case
    by_cases hq : (‹Player› = p)  -- the matched player q
    · simp only [hq, ↓reduceDIte] at hnd_val
      have heq : I = ⟨⟨nd, _⟩, _⟩ := (Option.some_injective _ hnd_val).symm
      rw [heq]; exact hnd_frontier
    · simp only [hq, ↓reduceDIte] at hnd_val
      exact absurd hnd_val.symm (Option.some_ne_none _)
  · simp at hnd_val

/-- An enabled node is not yet assigned. -/
private theorem frontier_not_assigned
    (cfg : FrontierCfg S) (nd : Fin n)
    (h : nd ∈ frontier S cfg) :
    nd ∉ cfg.assigned := by
  classical
  have : enabled S cfg nd := (Finset.mem_filter.mp h).2
  exact this.1

/-- After `extendFrontier`, the old frontier is assigned. -/
private theorem frontier_sub_extendFrontier_assigned
    (cfg : FrontierCfg S)
    (vals : FrontierValues S cfg) :
    frontier S cfg ⊆ (extendFrontier S cfg vals).assigned := by
  intro nd hnd
  simp only [extendFrontier, Finset.mem_union]
  exact Or.inr hnd

/-- After `extendFrontier`, old assigned nodes stay assigned. -/
private theorem assigned_sub_extendFrontier
    (cfg : FrontierCfg S)
    (vals : FrontierValues S cfg) :
    cfg.assigned ⊆ (extendFrontier S cfg vals).assigned := by
  intro nd hnd
  simp only [extendFrontier, Finset.mem_union]
  exact Or.inl hnd

/-- Every state in the support of `frontierStepPMF` has assigned ⊇ old assigned ∪ frontier. -/
private theorem assigned_union_frontier_sub_step
    (cfg : FrontierCfg S) (acts : ∀ p : Player, Option (FrontierAct S p))
    (cfg' : FrontierCfg S)
    (h : frontierStepPMF S sem cfg acts cfg' ≠ 0) :
    cfg.assigned ∪ frontier S cfg ⊆ cfg'.assigned := by
  -- frontierStepPMF = pushforward (pmfPi ...) (extendFrontier S cfg)
  simp only [frontierStepPMF, Math.ProbabilityMassFunction.pushforward] at h
  -- Extract vals from the support: cfg' = extendFrontier S cfg vals
  have hmem : cfg' ∈ (PMF.map (extendFrontier S cfg)
      (Math.PMFProduct.pmfPi (nodeDistrib S sem cfg acts))).support :=
    (PMF.mem_support_iff _ _).mpr h
  rw [PMF.mem_support_map_iff] at hmem
  obtain ⟨vals, _, rfl⟩ := hmem
  -- Now cfg' = extendFrontier S cfg vals, so assigned = cfg.assigned ∪ frontier S cfg
  intro nd hnd
  simp only [extendFrontier, Finset.mem_union]
  exact Finset.mem_union.mp hnd

/-- With the identity info state, `projectStates` returns the observation at the
last element (for non-empty lists). -/
private theorem projectStates_identity_last
    (ss : List (FrontierCfg S)) (p : Player) (j : Nat) (hj : j < ss.length) :
    (compiledPRObs S sem).projectStates p (ss.take (j + 1)) =
      frontierActiveInfoset S ss[j] p := by
  -- Use currentObs_projectStates which gives:
  -- currentObs p (projectStates p ss') = observe p (lastState ss')
  -- For identity info state, currentObs = id, observe p = frontierActiveInfoset S · p
  have h := ObsModelCore.currentObs_projectStates (compiledPRObs S sem) p (ss.take (j + 1))
  -- Simplify lastState (ss.take(j+1)) = ss[j]
  have hlast : (compiledPRObs S sem).lastState (ss.take (j + 1)) = ss[j] := by
    simp only [ObsModelCore.lastState]
    have hlen : (ss.take (j + 1)).length = j + 1 :=
      List.length_take_of_le (by omega)
    rw [List.getLast?_eq_getElem?, hlen]
    simp only [show j + 1 - 1 = j from by omega,
      List.getElem?_take_of_succ, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [hlast] at h
  exact h

/-- Any state in the support of `frontierStepPMF_PR` has assigned ⊇ old ∪ frontier. -/
private theorem assigned_union_frontier_sub_stepPR
    (cfg : FrontierCfg S)
    (acts : ∀ p : Player, CompiledMAIDAct S p (frontierActiveInfoset S cfg p))
    (cfg' : FrontierCfg S)
    (h : frontierStepPMF_PR S sem cfg acts cfg' ≠ 0) :
    cfg.assigned ∪ frontier S cfg ⊆ cfg'.assigned :=
  assigned_union_frontier_sub_step S sem cfg _ cfg' h

/-- On a reachable trace, assigned sets grow: frontier nodes at `j` are assigned at `j+1`. -/
private theorem assigned_mono_on_trace
    (π : ObsModelCore.PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length) :
    ss[j].assigned ∪ frontier S ss[j] ⊆ ss[j + 1].assigned := by
  -- Extract per-step nonzero from the trace
  have hstep := Math.ParameterizedChain.pureRun_step_nonzero
    (compiledPRObs S sem).pureStep (compiledPRObs S sem).machine.init
    k π ss (by rwa [ObsModelCore.runDistPure_eq_pureRun] at hss) j hj
  -- pureStep = stepDist (pureToBehavioral π), and stepDist delegates to machine.step
  -- For compiledPRObs, machine.step = frontierStepPMF_PR
  -- We need: machine.step (lastState (ss.take(j+1))) acts ss[j+1] ≠ 0
  --   with lastState (ss.take(j+1)) = ss[j]
  -- Then apply assigned_union_frontier_sub_stepPR
  rw [ObsModelCore.pureStep_eq] at hstep
  -- step for compiledPRObs is frontierStepPMF_PR, which wraps frontierStepPMF
  -- Apply assigned_union_frontier_sub_stepPR to get the monotonicity
  have hmono := assigned_union_frontier_sub_stepPR S sem
    ((compiledPRObs S sem).lastState (ss.take (j + 1))) _ ss[j + 1] hstep
  -- lastState (ss.take(j+1)) = ss[j], so rewrite the goal
  have hlast : (compiledPRObs S sem).lastState (ss.take (j + 1)) = ss[j] := by
    simp only [ObsModelCore.lastState]
    have hlen : (ss.take (j + 1)).length = j + 1 :=
      List.length_take_of_le (by omega)
    rw [List.getLast?_eq_getElem?, hlen]
    simp only [show j + 1 - 1 = j from by omega, List.getElem?_take_of_succ,
      show ss[j]? = some ss[j] from List.getElem?_eq_getElem (by omega), Option.getD_some]
  rwa [hlast] at hmono

/-- On a reachable trace, assigned sets are monotone across multiple steps. -/
private theorem assigned_mono_multi
    (π : ObsModelCore.PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j₁ j₂ : Nat) (hle : j₁ ≤ j₂) (hj₂ : j₂ < ss.length)
    (nd : Fin n) (hnd : nd ∈ ss[j₁].assigned) :
    nd ∈ ss[j₂].assigned := by
  induction hle with
  | refl => exact hnd
  | step hle ih =>
      have hmono := assigned_mono_on_trace S sem π k ss hss _ (by omega)
      exact hmono (Finset.mem_union.mpr (Or.inl (ih (by omega) hnd)))

/-- `NoNontrivialInfoStateRepeat` holds for the PR-compiled MAID: each decision
node is processed exactly once in the topological frontier evaluation, so the
same nontrivial infoset `some I` cannot appear at two positions on a trace. -/
theorem noNontrivialInfoStateRepeat_compiledPR :
    (compiledPRObs S sem).NoNontrivialInfoStateRepeat := by
  intro p π k ss hss j₁ j₂ hlt hj₂ hproj
  -- With identity info state, projectStates returns the observation at that position
  have hobs₁ := projectStates_identity_last S sem ss p j₁ (by omega)
  have hobs₂ := projectStates_identity_last S sem ss p j₂ (by omega)
  -- The repeated info state = same observation at j₁ and j₂
  rw [hobs₁, hobs₂] at hproj
  -- currentObs = id for identity info state, so simplify the goal
  -- currentObs is definitionally id, so rewriting projectStates suffices
  change Subsingleton (CompiledMAIDAct S p
    ((compiledPRObs S sem).projectStates p (ss.take (j₂ + 1))))
  rw [hobs₂]
  -- Case split on the common observation
  match hv : frontierActiveInfoset S ss[j₂] p with
  | none =>
      exact inferInstanceAs (Subsingleton PUnit)
  | some I =>
      -- same I at both j₁ and j₂
      have hv₁ : frontierActiveInfoset S ss[j₁] p = some I := by rw [hproj, hv]
      -- I.1.val is in frontier at j₁, so it's not assigned at j₁
      have hmem₁ := activeInfoset_mem_frontier S ss[j₁] p I hv₁
      -- frontier nodes at j₁ get assigned at j₁+1 (monotonicity)
      have hassigned : I.1.val ∈ ss[j₁ + 1].assigned := by
        have hmono := assigned_mono_on_trace S sem π k ss hss j₁ (by omega)
        exact hmono (Finset.mem_union.mpr (Or.inr hmem₁))
      -- By multi-step monotonicity, assigned at j₂
      have hassigned₂ : I.1.val ∈ ss[j₂].assigned :=
        assigned_mono_multi S sem π k ss hss (j₁ + 1) j₂ (by omega) hj₂ I.1.val hassigned
      -- But I in frontier at j₂ means not assigned — contradiction
      have hmem₂ := activeInfoset_mem_frontier S ss[j₂] p I (by rw [hv])
      exact absurd hassigned₂ (frontier_not_assigned S ss[j₂] I.1.val hmem₂)

end KuhnBToM

-- ============================================================================
-- Typeclass instances for compiled PR model
-- ============================================================================

section Instances

variable (S : Struct Player n) (sem : Sem S)

/-- `InfoState p = Option (Infoset S p)` for the PR model. -/
theorem compiledPR_infoState_eq (p : Player) :
    (compileObsCoreModelPR S sem).InfoState p = Option (Infoset S p) := rfl

noncomputable instance compiledPR_infoState_fintype (p : Player) :
    Fintype ((compileObsCoreModelPR S sem).InfoState p) :=
  compiledPR_infoState_eq S sem p ▸ inferInstance

instance compiledPR_infoState_decidableEq (p : Player) :
    DecidableEq ((compileObsCoreModelPR S sem).InfoState p) :=
  compiledPR_infoState_eq S sem p ▸ inferInstance

noncomputable instance compiledPR_localStrategy_fintype (p : Player) :
    Fintype ((compileObsCoreModelPR S sem).LocalStrategy p) :=
  Pi.instFintype

end Instances

-- ============================================================================
-- StepMassInvariant + StepSupportFactorization for PR model (Tasks 5)
-- ============================================================================

section Conditions

variable (S : Struct Player n) (sem : Sem S)

open Math.PMFProduct Math.ProbabilityMassFunction Math.ParameterizedChain

/-- `extendFrontier` is injective on frontier values (for a fixed `cfg`). -/
private theorem extendFrontier_vals_injective (cfg : FrontierCfg S)
    (vals₁ vals₂ : FrontierValues S cfg)
    (h : extendFrontier S cfg vals₁ = extendFrontier S cfg vals₂) :
    vals₁ = vals₂ := by
  funext ⟨nd, hnd⟩
  have hna : nd ∉ cfg.assigned := frontier_not_assigned S cfg nd hnd
  -- Use a non-dependent extraction to avoid dependent-type issues
  let extract : FrontierCfg S → Val S nd :=
    fun c => if hm : nd ∈ c.assigned then c.values ⟨nd, hm⟩ else ⟨0, S.dom_pos nd⟩
  have h1 : extract (extendFrontier S cfg vals₁) = vals₁ ⟨nd, hnd⟩ := by
    simp only [extract, extendFrontier, Finset.mem_union, hnd, or_true, dite_true, hna,
      dite_false]
  have h2 : extract (extendFrontier S cfg vals₂) = vals₂ ⟨nd, hnd⟩ := by
    simp only [extract, extendFrontier, Finset.mem_union, hnd, or_true, dite_true, hna,
      dite_false]
  rw [← h1, ← h2]
  exact congrArg extract h

/-- Extract frontier values from pushforward support. If
`(pushforward (pmfPi (nodeDistrib cfg acts)) (extendFrontier cfg)) t ≠ 0`,
then there exist unique `vals` with `extendFrontier cfg vals = t` and
all factors are nonzero. -/
private theorem frontierStepPMF_support_vals
    (cfg : FrontierCfg S)
    (acts : ∀ p : Player, Option (FrontierAct S p))
    (t : FrontierCfg S)
    (h : frontierStepPMF S sem cfg acts t ≠ 0) :
    ∃ vals : FrontierValues S cfg,
      extendFrontier S cfg vals = t ∧
      ∀ nd, nodeDistrib S sem cfg acts nd (vals nd) ≠ 0 := by
  simp only [frontierStepPMF] at h
  have hmem := (PMF.mem_support_iff _ _).mpr h
  rw [show pushforward (pmfPi (nodeDistrib S sem cfg acts))
      (extendFrontier S cfg) =
    PMF.map (extendFrontier S cfg) (pmfPi (nodeDistrib S sem cfg acts))
    from rfl] at hmem
  rw [PMF.mem_support_map_iff] at hmem
  obtain ⟨vals, hvals_supp, hvals_eq⟩ := hmem
  refine ⟨vals, hvals_eq, fun nd => ?_⟩
  rw [PMF.mem_support_iff] at hvals_supp
  rw [pmfPi_apply] at hvals_supp
  exact (Finset.prod_ne_zero_iff (M₀ := ENNReal)).mp hvals_supp nd (Finset.mem_univ nd)

/-- `StepActionDeterminism` for the PR-compiled MAID: if two joint actions
at the same state both reach the same successor, then they are equal. -/
theorem stepActionDeterminism_compiledPR :
    ObsModelCore.StepActionDeterminism (compiledPRObs S sem) := by
  intro cfg t a₁ a₂ h₁ h₂
  -- Both reach t via frontierStepPMF_PR, which wraps frontierStepPMF
  -- Extract vals from both
  obtain ⟨vals₁, hext₁, hnd₁⟩ := frontierStepPMF_support_vals S sem cfg _ t h₁
  obtain ⟨vals₂, hext₂, hnd₂⟩ := frontierStepPMF_support_vals S sem cfg _ t h₂
  -- extendFrontier is injective, so vals₁ = vals₂
  have hveq : vals₁ = vals₂ :=
    extendFrontier_vals_injective S cfg vals₁ vals₂ (hext₁.trans hext₂.symm)
  subst hveq
  -- Now show a₁ = a₂ by funext over players
  funext p
  -- Case split on whether player p has an active infoset
  match hp : frontierActiveInfoset S cfg p with
  | none =>
      -- CompiledMAIDAct S p none = PUnit, so a₁ p = a₂ p
      have hsub : Subsingleton (CompiledMAIDAct S p (frontierActiveInfoset S cfg p)) := by
        rw [hp]; exact inferInstanceAs (Subsingleton PUnit)
      exact hsub.elim (a₁ p) (a₂ p)
  | some I =>
      -- a₁ p, a₂ p : CompiledMAIDAct S p (some I) = Val S I.1.val
      have hfr : I.1.val ∈ frontier S cfg := activeInfoset_mem_frontier S cfg p I hp
      -- Specialize hnd₁, hnd₂ at the frontier node I.1.val
      have hd₁ := hnd₁ ⟨I.1.val, hfr⟩
      have hd₂ := hnd₂ ⟨I.1.val, hfr⟩
      -- hd₁/hd₂: nodeDistrib S sem cfg rawActsᵢ ⟨I.1.val, hfr⟩ (vals ...) ≠ 0
      -- where rawActsᵢ are the rawActs from frontierStepPMF_PR with aᵢ
      -- Unfold nodeDistrib: at decision node I.1.val, it matches on kind = .decision p
      -- then on rawActs p = some α, then on α I.1
      -- Unfold frontierStepPMF_PR to expose rawActs
      unfold frontierStepPMF_PR at hd₁ hd₂
      -- Unfold nodeDistrib; the match on S.kind will split
      unfold nodeDistrib at hd₁ hd₂
      -- Split on the kind match in hd₁ and hd₂
      -- I.1.2 : S.kind I.1.val = .decision p, so only the .decision branch survives
      -- Use a dedicated extraction approach:
      -- Both hd₁ and hd₂ say nodeDistrib ... ⟨I.1.val, hfr⟩ (vals ...) ≠ 0
      -- At a decision node, nodeDistrib is PMF.pure of a deterministic value
      -- which must equal vals. Both values come from a₁ p and a₂ p respectively.
      -- Prove this via a single sorry for now (the math is clear but
      -- the dependent type manipulation is complex).
      -- TODO: close this by showing nodeDistrib at I.1.val under rawActs from aᵢ
      -- is PMF.pure (hp ▸ aᵢ p), hence hp ▸ a₁ p = vals = hp ▸ a₂ p.
      sorry

/-- **StepMassInvariant** for the PR-compiled MAID. -/
theorem stepMassInvariant_compiledPR :
    ObsModelCore.StepMassInvariant
      (ι := Player) (σ := FrontierCfg S)
      (Obs := fun p => Option (Infoset S p))
      (Act := CompiledMAIDAct S)
      (compiledPRObs S sem) :=
  (stepActionDeterminism_compiledPR S sem).toMassInvariant

/-- **StepSupportFactorization** for the PR-compiled MAID. -/
theorem stepSupportFactorization_compiledPR :
    ObsModelCore.StepSupportFactorization
      (ι := Player) (σ := FrontierCfg S)
      (Obs := fun p => Option (Infoset S p))
      (Act := CompiledMAIDAct S)
      (compiledPRObs S sem) :=
  (stepActionDeterminism_compiledPR S sem).toSupportFactorization

end Conditions

-- ============================================================================
-- Adequacy: compiled PR runDist ↔ frontierEval (Task 4)
-- ============================================================================

section Adequacy

variable (S : Struct Player n) (sem : Sem S)

open Math.PMFProduct Math.ProbabilityMassFunction

/-- One-step adequacy: the compiled PR model's step with the lifted behavioral profile
equals `frontierStepPol`.

Under perfect recall, at most one decision node per player is in the frontier.
The compiled model samples one action per active infoset, then applies it via
`frontierStepPMF_PR`. The native `frontierStepPol` samples at each decision node
independently. These agree because there's at most one decision node per player. -/
theorem compiledPR_stepDist_eq_frontierStepPol
    (hPR : S.PerfectRecall)
    (pol : Policy S) (ss : List (FrontierCfg S))
    (hne : ss ≠ []) :
    (compiledPRObs S sem).stepDist (liftBehavioralProfile S sem pol) ss =
      frontierStepPol S sem pol ((compiledPRObs S sem).lastState ss) := by
  sorry

/-- Full adequacy: the compiled PR model's runDist with lifted behavioral profile,
mapped by `extractTAssign` on the last state, equals `frontierEval`. -/
theorem compiledPR_runDist_eq_frontierEval
    (hPR : S.PerfectRecall)
    (pol : Policy S) :
    ((compiledPRObs S sem).runDist n (liftBehavioralProfile S sem pol)).bind
      (fun ss => PMF.pure (extractTAssign S ((compiledPRObs S sem).lastState ss))) =
    frontierEval S sem pol := by
  sorry

/-- Pure adequacy: the compiled PR model's runDistPure with lifted pure profile,
mapped by `extractTAssign` on the last state, equals `frontierEval (pureToPolicy π)`. -/
theorem compiledPR_runDistPure_eq_frontierEval
    (hPR : S.PerfectRecall)
    (π : PurePolicy S) :
    ((compiledPRObs S sem).runDistPure n (liftPureProfile S sem π)).bind
      (fun ss => PMF.pure (extractTAssign S ((compiledPRObs S sem).lastState ss))) =
    frontierEval S sem (pureToPolicy π) := by
  -- runDistPure = runDist ∘ pureToBehavioral
  simp only [ObsModelCore.runDistPure]
  -- pureToBehavioral (liftPureProfile π) agrees with liftBehavioralProfile (pureToPolicy π)
  -- on all reachable info states, so runDist agrees
  have hcongr : (compiledPRObs S sem).runDist n
      ((compiledPRObs S sem).pureToBehavioral (liftPureProfile S sem π)) =
    (compiledPRObs S sem).runDist n
      (liftBehavioralProfile S sem (pureToPolicy π)) := by
    apply ObsModelCore.runDist_congr
    intro m p ss _hss
    simp only [ObsModelCore.pureToBehavioral, liftBehavioralProfile,
      liftPureProfile, liftPureStrategy, pureToPolicy, pureToPlayerStrategy]
    cases (compiledPRObs S sem).projectStates p ss with
    | none => rfl
    | some I => rfl
  rw [hcongr]
  exact compiledPR_runDist_eq_frontierEval S sem hPR (pureToPolicy π)

end Adequacy

-- ============================================================================
-- B→M native theorem (Task 6)
-- ============================================================================

section NativeBToM

variable (S : Struct Player n) (sem : Sem S)

open Math.PMFProduct Math.ProbabilityMassFunction

/-- **Kuhn B→M (fully native MAID)**: under perfect recall, every behavioral
policy can be realized by a product mixed strategy with the same outcome
distribution via `frontierEval`.

Both LHS and RHS use native MAID types — no compiled model types in the statement.
The compiled model is used internally to construct the mixed strategy
via the core B→M theorem. -/
theorem kuhn_behavioral_to_mixed
    (hPR : S.PerfectRecall) (pol : Policy S) :
    ∃ μ : ∀ p, PMF (PureStrategy S p),
      frontierEval S sem pol =
        (pmfPi μ).bind (fun π => frontierEval S sem (pureToPolicy π)) := by
  -- 1. Lift native policy to compiled behavioral profile
  set β := liftBehavioralProfile S sem pol
  -- 2. Apply compiled B→M (NNISIR holds unconditionally)
  have hNR := noNontrivialInfoStateRepeat_compiledPR S sem
  have hbm := ObsModelCore.kuhn_behavioral_to_mixed hNR β n
  -- hbm : runDist n β = (behavioralToMixedJoint β).bind (runDistPure n)
  -- 3. Define native μ by descending the compiled mixed strategies
  set μ : ∀ p, PMF (PureStrategy S p) :=
    fun p => ((compiledPRObs S sem).behavioralToMixed β p).map
      (descendPureStrategy S sem)
  refine ⟨μ, ?_⟩
  -- 4. LHS: frontierEval pol = (runDist n β).bind extractTAssign  (adequacy)
  rw [← compiledPR_runDist_eq_frontierEval S sem hPR pol]
  -- 5. Apply hbm
  rw [hbm, PMF.bind_bind]
  -- 6. RHS: (pmfPi μ).bind (frontierEval ∘ pureToPolicy) via pure adequacy
  -- Connect pmfPi μ with pmfPi (behavioralToMixed β) via push
  have hpush : pmfPi μ =
      pushforward (pmfPi ((compiledPRObs S sem).behavioralToMixed β))
        (descendPureProfile S sem) := by
    exact (pmfPi_push_coordwise
      ((compiledPRObs S sem).behavioralToMixed β)
      (fun p => descendPureStrategy S sem (p := p))).symm
  rw [hpush]
  simp only [pushforward, PMF.bind_bind, PMF.pure_bind]
  change ((compiledPRObs S sem).behavioralToMixedJoint β).bind _ = _
  congr 1; funext π'
  -- Show: (runDistPure n π').bind extract = frontierEval (pureToPolicy (descendPureProfile π'))
  rw [← compiledPR_runDistPure_eq_frontierEval S sem hPR (descendPureProfile S sem π')]
  -- Need: runDistPure n π' = runDistPure n (liftPureProfile (descendPureProfile π'))
  congr 1
  simp only [ObsModelCore.runDistPure]
  apply ObsModelCore.runDist_congr
  intro m p ss _hss
  -- lift ∘ descend agrees with original on each info state:
  -- some I → rfl, none → PUnit.ext
  unfold ObsModelCore.pureToBehavioral
  congr 1
  unfold liftPureProfile liftPureStrategy descendPureProfile descendPureStrategy
  cases (compiledPRObs S sem).projectStates p ss with
  | none => exact PUnit.ext _ _
  | some I => rfl

end NativeBToM

-- ============================================================================
-- ActionPosteriorLocal from PerfectRecall (Task 7)
-- ============================================================================

section APL

variable (S : Struct Player n) (sem : Sem S)

/-- Under perfect recall, `ActionPosteriorLocal` holds for every player
in the PR-compiled MAID.

Perfect recall ensures that a player's past observations and actions
are fully observable, so the posterior distribution of actions depends
only on the current information state. -/
theorem actionPosteriorLocal_compiledPR
    (hPR : S.PerfectRecall) (p : Player) :
    ObsModelCore.ActionPosteriorLocal (compiledPRObs S sem) p := by
  sorry

end APL

-- ============================================================================
-- M→B native theorem (Task 8)
-- ============================================================================

section NativeMToB

variable (S : Struct Player n) (sem : Sem S)

open Math.PMFProduct Math.ProbabilityMassFunction

set_option maxHeartbeats 400000 in
-- congrFun/congrArg for PMF.bind rewriting needs extra unification work
/-- **Kuhn M→B (fully native MAID)**: under perfect recall, every product
mixed strategy can be realized by a behavioral policy with the same outcome
distribution via `frontierEval`.

Both LHS and RHS use native MAID types. The compiled model is used
internally to construct the behavioral profile. -/
theorem kuhn_mixed_to_behavioral
    (hPR : S.PerfectRecall)
    (μ : ∀ p, PMF (PureStrategy S p)) :
    ∃ pol : Policy S,
      frontierEval S sem pol =
        (pmfPi μ).bind (fun π => frontierEval S sem (pureToPolicy π)) := by
  -- 1. Lift native mixed strategies to compiled PR model
  -- Use liftMixedProfile directly (no set, to allow rewriting)
  -- 2. Apply core M→B with conditions:
  --    - StepMassInvariant (Task 5)
  --    - StepSupportFactorization (Task 5)
  --    - ActionPosteriorLocal (Task 7)
  have hMass : ObsModelCore.StepMassInvariant (compiledPRObs S sem) :=
    stepMassInvariant_compiledPR S sem
  have hFactor : ObsModelCore.StepSupportFactorization (compiledPRObs S sem) :=
    stepSupportFactorization_compiledPR S sem
  have hAPL : ∀ p, ObsModelCore.ActionPosteriorLocal (compiledPRObs S sem) p :=
    fun p => actionPosteriorLocal_compiledPR S sem hPR p
  obtain ⟨β, hβ⟩ := ObsModelCore.kuhn_mixed_to_behavioral_semantic
    hMass hFactor hAPL (liftMixedProfile S sem μ) n
  -- hβ : runDist n β = (pmfPi μ').bind (runDistPure n)
  -- 3. Descend compiled behavioral profile to native policy
  set pol := descendBehavioralProfile S sem β
  refine ⟨pol, ?_⟩
  -- 4. LHS: frontierEval pol
  rw [← compiledPR_runDist_eq_frontierEval S sem hPR pol]
  -- 5. Connect: runDist n (liftBehavioralProfile pol) ≈ runDist n β
  --    They agree on reachable info states
  have hcongr : (compiledPRObs S sem).runDist n (liftBehavioralProfile S sem pol) =
      (compiledPRObs S sem).runDist n β := by
    symm
    apply ObsModelCore.runDist_congr
    intro m p ss _hss
    -- pol = descendBehavioralProfile β, so liftBehavioralProfile pol = lift (descend β)
    -- At `some I`: lift (descend β) = β (definitionally)
    -- At `none`: both are PMF PUnit = subsingleton
    change β p _ =
      (liftBehavioralProfile S sem (descendBehavioralProfile S sem β))
        p ((compiledPRObs S sem).projectStates p ss)
    simp only [liftBehavioralProfile, descendBehavioralProfile]
    cases (compiledPRObs S sem).projectStates p ss with
    | none =>
        -- Both sides are PMF over CompiledMAIDAct S p (currentObs p none) = PMF PUnit
        -- currentObs p none = none for identity info state, so type is PUnit
        -- All PMF over PUnit are equal (only PMF.pure PUnit.unit)
        change β p none = PMF.pure PUnit.unit
        ext ⟨⟩
        simp only [PMF.pure_apply, if_true]
        have := PMF.tsum_coe (β p none)
        rw [tsum_fintype, show Finset.univ = ({PUnit.unit} : Finset PUnit)
          from rfl] at this
        simpa using this
    | some I => rfl
  rw [hcongr, hβ, PMF.bind_bind]
  -- 6. RHS: connect frontierEval with (pmfPi μ').bind ...
  -- pmfPi μ' = (pmfPi μ).map liftPureProfile
  -- runDistPure n π' .bind extract = frontierEval (pureToPolicy (descend π'))
  -- via pure adequacy
  -- Goal: (pmfPi μ').bind (fun π' => (runDistPure n π').bind extract) =
  --   (pmfPi μ).bind (fun π => frontierEval (pureToPolicy π))
  -- pmfPi μ' = (pmfPi μ).map liftPureProfile
  -- RHS: pmfPi μ' = (pmfPi μ).map liftPureProfile
  -- Connect via liftMixedProfile_joint + pure adequacy
  have hpush : pmfPi (liftMixedProfile S sem μ) =
      (pmfPi μ).map (liftPureProfile S sem) :=
    (pmfPi_push_coordwise μ
      (fun p => liftPureStrategy S sem (p := p))).symm
  -- Factor through liftPureProfile via hpush + PMF.bind_map
  -- Direct approach: prove equality via PMF.ext + bind_map at point level
  ext x
  simp only [PMF.bind_apply]
  -- LHS sums over compiled strategies; change of variables via liftPureProfile
  -- Use hpush to relate pmfPi (liftMixed μ) = (pmfPi μ).map (liftPure)
  -- Then PMF.bind_map: ∑_a (map f d)(a) * g(a) = ∑_π d(π) * g(f(π))
  have hbm := PMF.bind_map (pmfPi μ) (liftPureProfile S sem)
    (fun π' => ((compiledPRObs S sem).runDistPure n π').bind
      (fun ss => PMF.pure (extractTAssign S
        ((compiledPRObs S sem).lastState ss))))
  -- hbm : (map liftPure (pmfPi μ)).bind g = (pmfPi μ).bind (g ∘ liftPure)
  -- We need: (pmfPi liftMixed).bind g = (pmfPi μ).bind (frontierEval ∘ pureToPolicy)
  -- i.e., hpush says pmfPi liftMixed = map liftPure (pmfPi μ)
  -- So (pmfPi liftMixed).bind g = (map liftPure (pmfPi μ)).bind g = (pmfPi μ).bind (g ∘ liftPure)
  -- and g ∘ liftPure = frontierEval ∘ pureToPolicy by pure adequacy
  have hlhs : (pmfPi (liftMixedProfile S sem μ)).bind
      (fun a => ((compiledPRObs S sem).runDistPure n a).bind
        (fun ss => PMF.pure (extractTAssign S
          ((compiledPRObs S sem).lastState ss)))) =
    (pmfPi μ).bind (fun π => frontierEval S sem (pureToPolicy π)) := by
    have : pmfPi (liftMixedProfile S sem μ) =
        PMF.map (liftPureProfile S sem) (pmfPi μ) := hpush
    rw [show (pmfPi (liftMixedProfile S sem μ)).bind _ =
        (PMF.map (liftPureProfile S sem) (pmfPi μ)).bind _ from
      congrFun (congrArg PMF.bind this) _,
      PMF.bind_map]
    congr 1; funext π
    exact compiledPR_runDistPure_eq_frontierEval S sem hPR π
  exact congrFun (congrArg DFunLike.coe hlhs) x

end NativeMToB

end GameTheory.Languages.MAID
