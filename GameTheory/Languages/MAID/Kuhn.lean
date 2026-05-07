import Math.PMFProduct
import GameTheory.Theorems.Kuhn
import GameTheory.Languages.MAID.CompileObs
import GameTheory.Languages.MAID.FrontierLemmas

/-!
# GameTheory.Languages.MAID.Kuhn

Kuhn reduction lemmas for compiled MAIDs via `ObsModelCore`.

## Main results

- `kuhn_behavioral_to_mixed_compiledPR` : B→M direction via `compileObsModelCorePR`,
  under `NoNontrivialInfoStateRepeat` (which holds for well-formed MAIDs)

## Architecture

**B→M** uses `compileObsModelCorePR`, which compiles MAIDs with observation-dependent
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
  compileObsModelCorePR S sem

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
    (compileObsModelCorePR S sem).InfoState p = Option (Infoset S p) := rfl

noncomputable instance compiledPR_infoState_fintype (p : Player) :
    Fintype ((compileObsModelCorePR S sem).InfoState p) :=
  compiledPR_infoState_eq S sem p ▸ inferInstance

instance compiledPR_infoState_decidableEq (p : Player) :
    DecidableEq ((compileObsModelCorePR S sem).InfoState p) :=
  compiledPR_infoState_eq S sem p ▸ inferInstance

noncomputable instance compiledPR_localStrategy_fintype (p : Player) :
    Fintype ((compileObsModelCorePR S sem).LocalStrategy p) :=
  Pi.instFintype

end Instances

-- ============================================================================
-- StepMassInvariant + StepSupportFactorization for PR model (Tasks 5)
-- ============================================================================

section Conditions

variable (S : Struct Player n) (sem : Sem S)

open Math.PMFProduct Math.ProbabilityMassFunction Math.ParameterizedChain

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

/-- Reduce a dependent match on `frontierActiveInfoset` when the result is known. -/
private theorem rawActs_match_eq
    (cfg : FrontierCfg S) (p : Player) (I : Infoset S p)
    (hp : frontierActiveInfoset S cfg p = some I)
    (a : CompiledMAIDAct S p (frontierActiveInfoset S cfg p)) :
    (match h : frontierActiveInfoset S cfg p with
      | none => (none : Option (FrontierAct S p))
      | some J => some fun d => if hd : d = J.fst then
          some (hd ▸ (show CompiledMAIDAct S p (some J) from h ▸ a)) else none) =
    some (fun d => if hd : d = I.fst then
          some (hd ▸ (show CompiledMAIDAct S p (some I) from hp ▸ a)) else none) := by
  split
  · next h => exact absurd (h.symm.trans hp) nofun
  · next J h =>
    have hJI : J = I := Option.some_injective _ (h.symm.trans hp)
    subst hJI; rfl

/-- At a decision node owned by player `p`, `nodeDistrib` with `rawActs` from
`frontierStepPMF_PR` is `PMF.pure (hp ▸ a p)` where `hp` witnesses the active
infoset. If the result is nonzero at some value `v`, then `v = hp ▸ a p`. -/
private theorem nodeDistrib_rawActs_eq
    (cfg : FrontierCfg S) (p : Player) (I : Infoset S p)
    (hp : frontierActiveInfoset S cfg p = some I)
    (hfr : I.1.val ∈ frontier S cfg)
    (a : (compiledPRObs S sem).JointActionAt cfg)
    (v : S.Val I.1.val) :
    nodeDistrib S sem cfg
      (fun q => match h : frontierActiveInfoset S cfg q with
        | none => none
        | some J => some fun d => if hd : d = J.fst then
            some (hd ▸ (show CompiledMAIDAct S q (some J) from h ▸ a q)) else none)
      ⟨I.1.val, hfr⟩ v ≠ 0 →
    v = (show CompiledMAIDAct S p (some I) from hp ▸ a p) := by
  intro hne
  unfold nodeDistrib at hne
  split at hne
  · next hch => exact absurd (hch.symm.trans I.1.2) nofun
  · next p₁ hk₁ =>
    -- Eliminate p₁ (reverse direction to keep p)
    have hp₁ : p = p₁ := (NodeKind.decision.inj (hk₁.symm.trans I.1.2)).symm; subst hp₁
    -- Beta-reduce the lambda application and use rawActs_match_eq
    have hraw := rawActs_match_eq S cfg p I hp (a p)
    dsimp only [] at hne
    rw [hraw] at hne
    simp only [show (⟨I.1.val, hk₁⟩ : DecisionNode S p) = I.fst from rfl,
      dite_true] at hne
    -- hne : PMF.pure (hp ▸ a p) v ≠ 0, extract v = hp ▸ a p
    simp only [PMF.pure_apply] at hne
    split at hne
    · assumption
    · exact absurd rfl hne
  · next hu => exact absurd (hu.symm.trans I.1.2) nofun

/-- `StepActionDeterminism` for the PR-compiled MAID: if two joint actions
at the same state both reach the same successor, then they are equal. -/
theorem stepActionDeterminism_compiledPR :
    ObsModelCore.StepActionDeterminism (compiledPRObs S sem) := by
  intro cfg t a₁ a₂ h₁ h₂
  obtain ⟨vals₁, hext₁, hnd₁⟩ := frontierStepPMF_support_vals S sem cfg _ t h₁
  obtain ⟨vals₂, hext₂, hnd₂⟩ := frontierStepPMF_support_vals S sem cfg _ t h₂
  have hveq : vals₁ = vals₂ :=
    extendFrontier_vals_injective S cfg vals₁ vals₂ (hext₁.trans hext₂.symm)
  subst hveq
  funext p
  match hp : frontierActiveInfoset S cfg p with
  | none =>
      have hsub : Subsingleton (CompiledMAIDAct S p (frontierActiveInfoset S cfg p)) := by
        rw [hp]; exact inferInstanceAs (Subsingleton PUnit)
      exact hsub.elim (a₁ p) (a₂ p)
  | some I =>
      have hfr : I.1.val ∈ frontier S cfg := activeInfoset_mem_frontier S cfg p I hp
      have hd₁ := hnd₁ ⟨I.1.val, hfr⟩
      have hd₂ := hnd₂ ⟨I.1.val, hfr⟩
      -- Both nodeDistrib are nonzero at vals₁ ⟨I.1.val, hfr⟩
      -- Extract: vals = hp ▸ a₁ p and vals = hp ▸ a₂ p
      have hv₁ := nodeDistrib_rawActs_eq S sem cfg p I hp hfr a₁ _ hd₁
      have hv₂ := nodeDistrib_rawActs_eq S sem cfg p I hp hfr a₂ _ hd₂
      -- hp ▸ a₁ p = hp ▸ a₂ p
      have heq : (hp ▸ a₁ p : CompiledMAIDAct S p (some I)) = hp ▸ a₂ p :=
        hv₁.symm.trans hv₂
      -- Injectivity of transport
      have inj : ∀ (obs : Option (Infoset S p)) (h : obs = some I)
        (x y : CompiledMAIDAct S p obs), h ▸ x = h ▸ y → x = y := by
        intro obs h x y heq; subst h; exact heq
      exact inj _ hp (a₁ p) (a₂ p) heq

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

/-- At a chance node, `nodeDistrib` equals `chanceCPD` (independent of `acts`). -/
private theorem nodeDistrib_at_chance
    (S : Struct Player n) (sem : Sem S) (cfg : FrontierCfg S)
    (acts : ∀ p : Player, Option (FrontierAct S p))
    (nd : ↥(frontier S cfg)) (hk : S.kind nd.1 = .chance) :
    nodeDistrib S sem cfg acts nd =
      sem.chanceCPD ⟨nd.1, hk⟩ (restrictCfg cfg (S.parents nd.1)
        (enabled_of_mem_frontier nd.2).2) := by
  simp only [nodeDistrib]; split
  · rfl
  · exact absurd (‹_› : S.kind nd.1 = .decision _) (by rw [hk]; exact nofun)
  · exact absurd (‹_› : S.kind nd.1 = .utility _) (by rw [hk]; exact nofun)

/-- At a utility node, `nodeDistrib` equals `PMF.pure utilityValue` (independent of `acts`). -/
private theorem nodeDistrib_at_utility
    (S : Struct Player n) (sem : Sem S) (cfg : FrontierCfg S)
    (acts : ∀ p : Player, Option (FrontierAct S p))
    (nd : frontier S cfg) (p : Player) (hk : S.kind nd.1 = .utility p) :
    nodeDistrib S sem cfg acts nd =
      PMF.pure (utilityValue S nd.1 ⟨p, hk⟩) := by
  simp only [nodeDistrib]; split
  · exact absurd (‹_› : S.kind nd.1 = .chance) (by rw [hk]; exact nofun)
  · exact absurd (‹_› : S.kind nd.1 = .decision _) (by rw [hk]; exact nofun)
  · rename_i q hkq
    have hqp : q = p := NodeKind.utility.inj (hkq.symm.trans hk)
    subst hqp; rfl

/-- At a decision node of player `p`, `nodeDistrib` depends only on `acts p`. -/
private theorem nodeDistrib_congr_decision
    (S : Struct Player n) (sem : Sem S) (cfg : FrontierCfg S)
    (acts₁ acts₂ : ∀ p : Player, Option (FrontierAct S p))
    (nd : ↥(frontier S cfg)) (p : Player)
    (hk : S.kind nd.1 = .decision p)
    (h : acts₁ p = acts₂ p) :
    nodeDistrib S sem cfg acts₁ nd = nodeDistrib S sem cfg acts₂ nd := by
  simp only [nodeDistrib]
  split
  · rfl  -- chance
  · rename_i q hkq
    have hqp : q = p := NodeKind.decision.inj (hkq.symm.trans hk)
    subst hqp; rw [h]
  · exact absurd (‹_› : S.kind nd.1 = .utility _) (by rw [hk]; exact nofun)

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
    (pol : Policy S) (ss : List (FrontierCfg S)) :
    (compiledPRObs S sem).stepDist (liftBehavioralProfile S sem pol) ss =
      frontierStepPol S sem pol ((compiledPRObs S sem).lastState ss) := by
  set O := compiledPRObs S sem
  set cfg := O.lastState ss
  -- For identity info state: projectStates p ss = frontierActiveInfoset S cfg p
  have hproj : ∀ p, O.projectStates p ss = frontierActiveInfoset S cfg p :=
    fun p => O.currentObs_projectStates p ss
  -- Abbreviate the rawActs conversion from frontierStepPMF_PR
  set rawActs : (∀ p, CompiledMAIDAct S p (frontierActiveInfoset S cfg p)) →
      ∀ p, Option (FrontierAct S p) :=
    fun acts p => match h : frontierActiveInfoset S cfg p with
      | none => none
      | some I => some fun d => if hd : d = I.fst then
          some (hd ▸ (show CompiledMAIDAct S p (some I) from h ▸ acts p)) else none
  -- The nodeDistrib function for a given player action profile
  set G : (∀ p, CompiledMAIDAct S p (frontierActiveInfoset S cfg p)) →
      ∀ nd : ↥(frontier S cfg), PMF (S.Val nd.1) :=
    fun acts nd => nodeDistrib S sem cfg (rawActs acts) nd
  -- Step 1: Reduce to inner product equality by factoring out pushforward.
  -- LHS = (jointActionDist).bind (fun a => pushforward (pmfPi (G a)) extend)
  --      = pushforward ((jointActionDist).bind (fun a => pmfPi (G a))) extend
  -- RHS = pushforward (pmfPi nodeDistPol) extend
  -- Both are pushforward through extend, so suffices: inner match.
  suffices h_inner :
      (O.jointActionDist (liftBehavioralProfile S sem pol) ss).bind
        (fun a => pmfPi (G (O.castJointAction ss a))) =
        pmfPi (nodeDistPol S sem pol cfg) by
    simp only [ObsModelCore.stepDist, frontierStepPol]
    change (O.jointActionDist _ ss).bind (fun a =>
        frontierStepPMF_PR S sem cfg (O.castJointAction ss a)) =
      pushforward (pmfPi (nodeDistPol S sem pol cfg)) (extendFrontier S cfg)
    conv_lhs =>
      arg 2; ext a
      change pushforward (pmfPi (G (O.castJointAction ss a))) (extendFrontier S cfg)
    rw [← Math.ProbabilityMassFunction.pushforward_bind]
    exact congrArg (pushforward · (extendFrontier S cfg)) h_inner
  -- Step 2: Apply pmfPi_bind_pmfPi_of_disjoint_coords
  -- to factor the bind over players into a product over nodes.
  -- Define H a nd = G (castJointAction a) nd, which maps player actions to node distros.
  set H := fun a nd => G (O.castJointAction ss a) nd with hH_def
  -- Define coord: which player "owns" each frontier node
  set coord : ↥(frontier S cfg) → Option Player := fun nd =>
    match S.kind nd.1 with
    | .decision p => some p
    | _ => none
  -- Apply the routing theorem
  have hroute := pmfPi_bind_pmfPi_of_disjoint_coords
    (fun p => (liftBehavioralProfile S sem pol) p (O.projectStates p ss))
    H coord
    (fun nd hc j => ?h_const)
    (fun nd i hc j hne => ?h_single)
    (fun k₁ k₂ i hc₁ hc₂ => ?h_inj)
  · -- Use the routing result
    simp only [ObsModelCore.jointActionDist]
    change (pmfPi fun p => liftBehavioralProfile S sem pol p (O.projectStates p ss)).bind
        (fun a => pmfPi (H a)) =
      pmfPi (nodeDistPol S sem pol cfg)
    conv_lhs => rw [show ((pmfPi fun p => liftBehavioralProfile S sem pol p
        (O.projectStates p ss)).bind fun a => pmfPi (H a)) =
      pmfPi (fun k => (pmfPi fun p => liftBehavioralProfile S sem pol p
        (O.projectStates p ss)).bind fun a => H a k) from hroute]
    -- Now: pmfPi (fun nd => marginal) = pmfPi nodeDistPol
    congr 1; funext nd
    -- Step 3: per-node marginal agreement
    -- For chance/utility, H a nd is constant in a, so the bind collapses.
    -- For decision nodes, the bind marginal equals pol p I.
    -- First, determine the node kind.
    match hk : S.kind nd.1 with
    | .chance =>
      -- H a nd = chanceCPD (constant, doesn't use a) by nodeDistrib_at_chance
      conv_lhs => arg 2; ext a; rw [show H a nd =
        nodeDistrib S sem cfg (rawActs (O.castJointAction ss a)) nd from rfl,
        nodeDistrib_at_chance S sem cfg _ nd hk]
      simp only [PMF.bind_const]
      -- RHS
      simp only [nodeDistPol]; split
      · rfl
      · exact absurd (‹_› : S.kind nd.1 = .decision _) (by rw [hk]; exact nofun)
      · exact absurd (‹_› : S.kind nd.1 = .utility _) (by rw [hk]; exact nofun)
    | .decision p =>
      rw [nodeDistPol_at_decision sem pol cfg nd p hk hk
        (fun x hx => (enabled_of_mem_frontier nd.2).2 (S.obs_sub nd.1 hx))]
      -- Use the canonical form of frontierActiveInfoset
      have hactive := frontierActiveInfoset_eq_canonical hPR nd.2 p hk
        (fun x hx => (enabled_of_mem_frontier nd.2).2 (S.obs_sub nd.1 hx))
      have hprojq : O.projectStates p ss =
          some ⟨⟨nd.1, hk⟩, restrictCfg cfg (S.obsParents nd.1)
            (fun x hx => (enabled_of_mem_frontier nd.2).2 (S.obs_sub nd.1 hx))⟩ := by
        rw [hproj p, hactive]
      -- Prove H a nd HEq PMF.pure (a p) by resolving all dependent matches
      have hH_heq : ∀ a, HEq (H a nd) (PMF.pure (a p) :
          PMF (CompiledMAIDAct S p (O.projectStates p ss))) := by
        intro a; simp only [H, G, nodeDistrib]
        split
        · exact absurd (‹_› : S.kind nd.1 = .chance) (by rw [hk]; exact nofun)
        · rename_i q hkq
          simp_all only [O, cfg, H, G, rawActs]
          obtain ⟨val, property⟩ := nd
          simp_all only [cfg, O]
          split
          next x α heq =>
            split
            next x_1 v heq_1 =>
              simp_all only
              split at heq
              next heq_2 => simp_all only [reduceCtorEq]
              next J heq_2 =>
                simp_all only [Option.some.injEq]
                subst heq
                simp_all only [Option.dite_none_right_eq_some, Option.some.injEq]
                obtain ⟨w, h⟩ := heq_1
                subst h
                simp only [ObsModelCore.castJointAction]
                apply Math.ProbabilityMassFunction.pure_heq
                simp_all only [eqRec_heq_iff_heq]
                grind only
            next x_1 heq_1 =>
              simp_all only
              split at heq
              next heq_2 => simp_all only [reduceCtorEq]
              next J heq_2 =>
                simp_all only [Option.some.injEq]
                subst heq
                simp_all only [dite_eq_right_iff, reduceCtorEq, imp_false]
                -- heq_1 : ¬⟨val, ⋯⟩ = J.fst, but J = canonical infoset so J.fst.val = val
                have hqp : q = p := NodeKind.decision.inj (hkq.symm.trans hk)
                subst hqp
                have := Option.some_injective _ (heq_2.symm.trans hactive)
                exact absurd (congrArg Sigma.fst this ▸ Subtype.ext rfl) heq_1
          next x heq =>
            simp_all only [NodeKind.decision.injEq]
            subst hkq
            split at heq
            next heq_1 => simp_all only [reduceCtorEq]
            next J heq_1 => simp_all only [Option.some.injEq, reduceCtorEq]
        · exact absurd (‹_› : S.kind nd.1 = .utility _) (by rw [hk]; exact nofun)
      -- Now work at ext level
      -- Work at the PMF level, not pointwise
      -- hH_heq : ∀ a, H a nd ≍ PMF.pure (a p)
      -- So the bind with H ≍ the bind with PMF.pure (· p)
      have hbind_heq : HEq
          ((pmfPi fun i => liftBehavioralProfile S sem pol i
            (O.projectStates i ss)).bind (fun a => H a nd))
          ((pmfPi fun i => liftBehavioralProfile S sem pol i
            (O.projectStates i ss)).bind (fun a => PMF.pure (a p))) := by
        exact Math.ProbabilityMassFunction.bind_heq _
          (congrArg (CompiledMAIDAct S p) hprojq.symm) hH_heq
      -- The RHS bind collapses to the p-th marginal
      have hbind_eq : ((pmfPi fun i => liftBehavioralProfile S sem pol i
            (O.projectStates i ss)).bind (fun a => PMF.pure (a p))) =
          liftBehavioralProfile S sem pol p (O.projectStates p ss) := by
        rw [pmfPi_bind_eval]; exact PMF.bind_pure _
      -- Combine: LHS ≍ marginal = pol p I_nd
      -- Chain: LHS ≍ bind(PMF.pure ∘ proj p) = marginal p = pol p I_nd
      have hfinal : HEq
          ((pmfPi fun i => liftBehavioralProfile S sem pol i (O.projectStates i ss)).bind
            (fun a => H a nd))
          (liftBehavioralProfile S sem pol p (O.projectStates p ss)) :=
        hbind_heq.trans (heq_of_eq hbind_eq)
      -- hfinal : LHS ≍ liftBehavioral pol p (projectStates p ss) : PMF (CompiledMAIDAct ...)
      -- After rw [hprojq], liftBehavioral reduces to pol p I_nd : PMF (S.Val nd.1)
      -- Since LHS : PMF (S.Val nd.1) and pol p I_nd : PMF (S.Val nd.1), eq_of_heq works
      exact eq_of_heq (hfinal.trans (by rw [hprojq]; exact HEq.rfl))
    | .utility p =>
      conv_lhs => arg 2; ext a; rw [show H a nd =
        nodeDistrib S sem cfg (rawActs (O.castJointAction ss a)) nd from rfl,
        nodeDistrib_at_utility S sem cfg _ nd p hk]
      simp only [PMF.bind_const]
      simp only [nodeDistPol]; split
      · exact absurd (‹_› : S.kind nd.1 = .chance) (by rw [hk]; exact nofun)
      · exact absurd (‹_› : S.kind nd.1 = .decision _) (by rw [hk]; exact nofun)
      · rename_i q hkq
        have : q = p := NodeKind.utility.inj (hkq.symm.trans hk)
        subst this; rfl
  · -- h_const: chance/utility nodes ignore all player coordinates
    -- coord nd = none means S.kind nd ≠ .decision _
    -- nodeDistrib at chance/utility doesn't use rawActs at all
    intro s x
    simp only [H, G, nodeDistrib]
    split
    · rfl  -- chance: uses chanceCPD, independent of acts
    · -- decision p: contradicts coord nd = none
      rename_i p hk
      exact absurd (show coord nd = some p from by simp [coord, hk]) (by rw [hc]; exact nofun)
    · rfl  -- utility: uses PMF.pure utilityValue, independent of acts
  · -- h_single: decision node of player i, H a nd depends only on a i
    classical
    intro s x
    have hk : S.kind nd.1 = .decision i := by
      simp only [coord] at hc
      match hk : S.kind nd.1, hc with
      | .decision p, h => exact congrArg NodeKind.decision (Option.some_injective _ h)
    simp only [H, G]
    apply nodeDistrib_congr_decision S sem cfg _ _ nd i hk
    simp only [rawActs]
    split
    · rfl
    · congr 1; funext d
      split
      · congr 1; congr 1; congr 1
        simp only [ObsModelCore.castJointAction]
        congr 1
        simp [Function.update, Ne.symm hne]
      · rfl
  · -- h_inj: at most one decision node per player (PerfectRecall)
    -- coord k = some i means S.kind k = .decision i
    have hk₁ : S.kind k₁.1 = .decision i := by
      simp only [coord] at hc₁
      match hk : S.kind k₁.1, hc₁ with
      | .decision p, h => exact congrArg NodeKind.decision (Option.some_injective _ h)
    have hk₂ : S.kind k₂.1 = .decision i := by
      simp only [coord] at hc₂
      match hk : S.kind k₂.1, hc₂ with
      | .decision p, h => exact congrArg NodeKind.decision (Option.some_injective _ h)
    exact Subtype.ext
      (frontier_unique_decision_per_player S hPR cfg i k₁.1 k₂.1 k₁.2 k₂.2 hk₁ hk₂)

/-- Full adequacy: the compiled PR model's runDist with lifted behavioral profile,
mapped by `extractTAssign` on the last state, equals `frontierEval`. -/
theorem compiledPR_runDist_eq_frontierEval
    (hPR : S.PerfectRecall)
    (pol : Policy S) :
    ((compiledPRObs S sem).runDist n (liftBehavioralProfile S sem pol)).bind
      (fun ss => PMF.pure (extractTAssign S ((compiledPRObs S sem).lastState ss))) =
    frontierEval S sem pol := by
  set β := liftBehavioralProfile S sem pol
  set O := compiledPRObs S sem
  -- Main claim: (runDist k β).bind (fun ss => pure (lastState ss)) = iterate^k
  suffices hmain : ∀ k : Nat,
      (O.runDist k β).bind (fun ss => PMF.pure (O.lastState ss)) =
      (fun d => d.bind (frontierStepPol S sem pol))^[k]
        (PMF.pure (initialCfg S)) by
    -- LHS = bind (fun ss => pure (extract (lastState ss)))
    --     = (bind (fun ss => pure (lastState ss))).bind (fun s => pure (extract s))  [bind_bind]
    --     = (hmain n).bind (fun s => pure (extract s))
    --     = frontierEval  [definition, since map f = bind (pure ∘ f)]
    conv_lhs =>
      arg 2; ext ss
      rw [show PMF.pure (extractTAssign S (O.lastState ss)) =
          (PMF.pure (O.lastState ss)).bind (fun s => PMF.pure (extractTAssign S s))
        from by simp only [PMF.pure_bind]]
    rw [← PMF.bind_bind, hmain, Math.PMFIter.nat_iterate_bind_pure_eq_iter]
    rfl
  intro k
  induction k with
  | zero =>
    change (PMF.pure [O.init]).bind _ = _
    rw [PMF.pure_bind]; rfl
  | succ k ih =>
    simp only [ObsModelCore.runDist, Math.TraceRun.traceRun]
    rw [PMF.bind_bind]
    conv_lhs =>
      arg 2; ext ss
      rw [show (Math.ProbabilityMassFunction.pushforward (O.stepDist β ss)
            (fun t => ss ++ [t])).bind
              (fun ss' => PMF.pure (O.lastState ss')) =
            O.stepDist β ss from by
          rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_map]
          simp [Function.comp_def, ObsModelCore.lastState_append_singleton, PMF.bind_pure]]
    conv_lhs =>
      arg 2; ext ss
      rw [compiledPR_stepDist_eq_frontierStepPol S sem hPR pol ss]
    change (O.runDist k β).bind (fun ss =>
        frontierStepPol S sem pol (O.lastState ss)) =
      (fun d => d.bind (frontierStepPol S sem pol))^[k + 1] (PMF.pure (initialCfg S))
    conv_lhs =>
      arg 2; ext ss
      rw [show frontierStepPol S sem pol (O.lastState ss) =
          (PMF.pure (O.lastState ss)).bind (frontierStepPol S sem pol)
        from (PMF.pure_bind _ _).symm]
    rw [← PMF.bind_bind, ih, Function.iterate_succ', Function.comp_apply]

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
  rw [pushforward]
  trans (pmfPi (ObsModelCore.behavioralToMixed β)).bind
      (fun π' => frontierEval S sem (pureToPolicy (descendPureProfile S sem π')))
  · unfold ObsModelCore.behavioralToMixedJoint
    apply bind_congr_on_support
    intro π' _hπ'
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
  · exact (PMF.bind_map (pmfPi (ObsModelCore.behavioralToMixed β))
      (descendPureProfile S sem)
      (fun π => frontierEval S sem (pureToPolicy π))).symm

end NativeBToM

-- ============================================================================
-- ActionPosteriorLocal from PerfectRecall (Task 7)
-- ============================================================================

section APL

variable (S : Struct Player n) (sem : Sem S)

open Math.ParameterizedChain ObsModelCore

/-- Any state in the support of `frontierStepPMF` has assigned = old ∪ frontier. -/
private theorem assigned_eq_step
    (cfg : FrontierCfg S) (acts : ∀ p : Player, Option (FrontierAct S p))
    (cfg' : FrontierCfg S)
    (h : frontierStepPMF S sem cfg acts cfg' ≠ 0) :
    cfg'.assigned = cfg.assigned ∪ MAID.frontier S cfg := by
  simp only [frontierStepPMF, Math.ProbabilityMassFunction.pushforward] at h
  have hmem : cfg' ∈ (PMF.map (extendFrontier S cfg)
      (Math.PMFProduct.pmfPi (nodeDistrib S sem cfg acts))).support :=
    (PMF.mem_support_iff _ _).mpr h
  rw [PMF.mem_support_map_iff] at hmem
  obtain ⟨vals, _, rfl⟩ := hmem
  rfl

/-- On a feasible trace, the first element is the initial config. -/
private theorem pureRun_getElem_zero
    (π : PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : pureRun (compiledPRObs S sem).pureStep (compiledPRObs S sem).init k π ss ≠ 0)
    (h0 : 0 < ss.length) :
    ss[0] = (compiledPRObs S sem).init := by
  induction k generalizing ss with
  | zero =>
    have : ss = [(compiledPRObs S sem).init] := by
      by_contra hne; exact hss (by simp [pureRun, PMF.pure_apply, hne])
    simp [this]
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨pre, t, hcat⟩
    · simp at h0
    · rw [List.concat_eq_append] at hcat; subst hcat
      have hpre := left_ne_zero_of_mul (pureRun_succ_append .. ▸ hss)
      have hlen_pre : pre.length = m + 1 := pureRun_length _ _ m π pre hpre
      simp only [List.getElem_append_left (show 0 < pre.length by omega)]
      exact ih pre hpre (by omega)

/-- On a feasible trace, `assigned` at step `j+1` equals `assigned ∪ frontier` at step `j`. -/
private theorem lastState_take_eq
    (ss : List (FrontierCfg S)) (j : Nat) (hj : j < ss.length) :
    (compiledPRObs S sem).lastState (ss.take (j + 1)) = ss[j] := by
  simp only [ObsModelCore.lastState]
  have hlen : (ss.take (j + 1)).length = j + 1 :=
    List.length_take_of_le (by omega)
  rw [List.getLast?_eq_getElem?, hlen]
  simp only [show j + 1 - 1 = j from by omega, List.getElem?_take_of_succ,
    show ss[j]? = some ss[j] from List.getElem?_eq_getElem hj, Option.getD_some]

/-- Any state in the support of `frontierStepPMF_PR` has assigned = old ∪ frontier. -/
private theorem assigned_eq_stepPR
    (cfg : FrontierCfg S)
    (acts : ∀ p : Player, CompiledMAIDAct S p (frontierActiveInfoset S cfg p))
    (cfg' : FrontierCfg S)
    (h : frontierStepPMF_PR S sem cfg acts cfg' ≠ 0) :
    cfg'.assigned = cfg.assigned ∪ MAID.frontier S cfg :=
  assigned_eq_step S sem cfg _ cfg' h

/-- `frontierStepPMF` preserves values at already-assigned nodes. -/
private theorem frontierStepPMF_preserves_old
    (cfg : FrontierCfg S) (acts : ∀ p : Player, Option (FrontierAct S p))
    (cfg' : FrontierCfg S)
    (h : frontierStepPMF S sem cfg acts cfg' ≠ 0)
    (nd : Fin n) (h₁ : nd ∈ cfg.assigned) (h₂ : nd ∈ cfg'.assigned) :
    cfg'.values ⟨nd, h₂⟩ = cfg.values ⟨nd, h₁⟩ := by
  obtain ⟨vals, hext, _⟩ := frontierStepPMF_support_vals S sem cfg acts cfg' h
  subst hext
  exact extendFrontier_preserves_old S cfg vals nd h₁ h₂

private theorem assigned_eq_on_trace_step
    (π : PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length) :
    ss[j + 1].assigned = ss[j].assigned ∪ MAID.frontier S ss[j] := by
  have hstep := pureRun_step_nonzero
    (compiledPRObs S sem).pureStep (compiledPRObs S sem).machine.init
    k π ss (by rwa [runDistPure_eq_pureRun] at hss) j hj
  rw [ObsModelCore.pureStep_eq] at hstep
  have hlast := lastState_take_eq S sem ss j (by omega)
  have hmono := assigned_eq_stepPR S sem
    ((compiledPRObs S sem).lastState (ss.take (j + 1))) _ ss[j + 1] hstep
  rwa [hlast] at hmono

/-- Two feasible traces from the same init have the same `assigned` at each step. -/
private theorem assigned_eq_on_traces
    (π₁ π₂ : PureProfile (compiledPRObs S sem))
    (k₁ k₂ : Nat) (ss₁ ss₂ : List (FrontierCfg S))
    (h₁ : (compiledPRObs S sem).runDistPure k₁ π₁ ss₁ ≠ 0)
    (h₂ : (compiledPRObs S sem).runDistPure k₂ π₂ ss₂ ≠ 0)
    (j : Nat) (hj₁ : j < ss₁.length) (hj₂ : j < ss₂.length) :
    ss₁[j].assigned = ss₂[j].assigned := by
  induction j with
  | zero =>
    have h0₁ := pureRun_getElem_zero S sem π₁ k₁ ss₁
      (by rwa [runDistPure_eq_pureRun] at h₁) hj₁
    have h0₂ := pureRun_getElem_zero S sem π₂ k₂ ss₂
      (by rwa [runDistPure_eq_pureRun] at h₂) hj₂
    rw [h0₁, h0₂]
  | succ m ih =>
    have hih := ih (by omega) (by omega)
    rw [assigned_eq_on_trace_step S sem π₁ k₁ ss₁ h₁ m hj₁,
        assigned_eq_on_trace_step S sem π₂ k₂ ss₂ h₂ m hj₂,
        hih, frontier_eq_of_assigned_eq S ss₁[m] ss₂[m] hih]

/-- Obs-parent values are recorded in the infoset: if `frontierActiveInfoset` returns
`some I` and `nd ∈ obsParents I.1.val`, then `cfg.values ⟨nd, _⟩ = I.2 ⟨nd, hnd⟩`. -/
private theorem activeInfoset_obsParent_value
    (cfg : FrontierCfg S) (p : Player) (I : Infoset S p)
    (hact : frontierActiveInfoset S cfg p = some I)
    (nd : Fin n) (hnd : nd ∈ S.obsParents I.1.val)
    (hmem : nd ∈ cfg.assigned) :
    cfg.values ⟨nd, hmem⟩ = I.2 ⟨nd, hnd⟩ := by
  simp only [frontierActiveInfoset] at hact
  have hMem : I ∈ frontierInfosets S cfg p := List.mem_of_head? hact
  simp only [frontierInfosets] at hMem
  rw [List.mem_filterMap] at hMem
  obtain ⟨nd', hnd'_mem, hnd'_val⟩ := hMem
  have hnd'_fr : nd' ∈ MAID.frontier S cfg := Finset.mem_toList.mp hnd'_mem
  simp only [hnd'_fr, dite_true] at hnd'_val
  -- I comes from frontierInfosets: I = ⟨⟨nd', _⟩, restrictCfg cfg (obsParents nd') _⟩
  -- So I.2 ⟨nd, hnd⟩ = restrictCfg cfg (obsParents nd') _ ⟨nd, _⟩ = cfg.values ⟨nd, _⟩
  -- Both sides are cfg.values ⟨nd, _⟩ with different membership proofs → congr
  -- Use the fact that the filterMap body constructs restrictCfg
  -- Direct approach: show I.2 ⟨nd, hnd⟩ = cfg.values ⟨nd, _⟩ by unfolding restrictCfg
  suffices h : ∃ (hpar : S.obsParents I.1.val ⊆ cfg.assigned),
      I.2 = restrictCfg cfg (S.obsParents I.1.val) hpar by
    obtain ⟨hpar, heq⟩ := h
    rw [heq]; simp [restrictCfg]
  -- Extract from the frontierInfosets construction
  revert hnd'_val; intro hnd'_val
  split at hnd'_val
  · -- .decision q case
    next q hk₁ =>
    split at hnd'_val
    · next hq =>
      subst hq
      have hIeq : I = ⟨⟨nd', _⟩, restrictCfg cfg (S.obsParents nd') _⟩ :=
        (Option.some_injective _ hnd'_val).symm
      subst hIeq
      -- I.fst = ⟨nd', hk₁⟩, so obsParents I.fst = obsParents nd'
      -- Need: obsParents nd' ⊆ cfg.assigned
      have hen : enabled S cfg nd' := by simpa [MAID.frontier] using hnd'_fr
      exact ⟨fun x hx => hen.2 (S.obs_sub nd' hx), rfl⟩
    · simp at hnd'_val
  · -- non-decision cases
    simp at hnd'_val

/-- `frontierActiveInfoset` depends only on `assigned` and the values at obs-parents:
if two configs have the same assigned set and agree on obs-parent values, they
produce the same active infoset. -/
private theorem frontierActiveInfoset_eq_of_assigned_vals_eq
    (cfg₁ cfg₂ : FrontierCfg S) (p : Player)
    (hassn : cfg₁.assigned = cfg₂.assigned)
    (hvals : ∀ nd (h₁ : nd ∈ cfg₁.assigned) (h₂ : nd ∈ cfg₂.assigned),
      cfg₁.values ⟨nd, h₁⟩ = cfg₂.values ⟨nd, h₂⟩) :
    frontierActiveInfoset S cfg₁ p = frontierActiveInfoset S cfg₂ p := by
  suffices hInfosets : frontierInfosets S cfg₁ p = frontierInfosets S cfg₂ p by
    simp only [frontierActiveInfoset, hInfosets]
  unfold frontierInfosets
  have hfr := frontier_eq_of_assigned_eq S cfg₁ cfg₂ hassn
  rw [show (MAID.frontier S cfg₂).toList = (MAID.frontier S cfg₁).toList from by rw [hfr]]
  apply List.filterMap_congr
  intro nd hnd
  -- nd ∈ (frontier S cfg₁).toList
  have hnd_fr : nd ∈ MAID.frontier S cfg₁ := by
    rwa [Finset.mem_toList] at hnd
  have hnd_fr₂ : nd ∈ MAID.frontier S cfg₂ := by rw [← hfr]; exact hnd_fr
  simp only [hnd_fr, hnd_fr₂, dite_true]
  split <;> try rfl
  next q hk =>
    by_cases hq : q = p
    · simp only [hq, dite_true]
      have hen₁ : enabled S cfg₁ nd := by simpa [MAID.frontier] using hnd_fr
      have hen₂ : enabled S cfg₂ nd := by simpa [MAID.frontier] using hnd_fr₂
      simp only [Option.some.injEq]
      refine Sigma.ext rfl (heq_of_eq (funext fun ⟨x, hx⟩ => ?_))
      simp only [restrictCfg]
      exact hvals x (hen₁.2 (S.obs_sub nd hx)) (hen₂.2 (S.obs_sub nd hx))
    · simp [hq]

/-- If two filterMap functions agree on the none/some pattern and the first
`some` value is the same, then `head?` of the filterMap results is the same. -/
private theorem filterMap_head?_eq_of_none_agree {α β : Type*}
    (f₁ f₂ : α → Option β) (L : List α) (b : β)
    (hact : (L.filterMap f₂).head? = some b)
    (hnone : ∀ a ∈ L, f₂ a = none → f₁ a = none)
    (hsome : ∀ a ∈ L, f₂ a = some b → f₁ a = some b) :
    (L.filterMap f₁).head? = some b := by
  induction L with
  | nil => simp at hact
  | cons hd tl ih =>
    simp only [List.filterMap_cons] at hact ⊢
    cases hf₂ : f₂ hd with
    | none =>
      have hf₁ := hnone hd (List.mem_cons_self ..) hf₂
      rw [hf₁]
      rw [hf₂] at hact
      exact ih hact
        (fun a ha => hnone a (List.mem_cons_of_mem _ ha))
        (fun a ha => hsome a (List.mem_cons_of_mem _ ha))
    | some val =>
      rw [hf₂] at hact
      simp only [List.head?_cons, Option.some.injEq] at hact
      subst hact
      have hf₁ := hsome hd (List.mem_cons_self ..) hf₂
      rw [hf₁]
      simp [List.head?_cons]

/-- If `frontierActiveInfoset S cfg₂ p = some I` and `cfg₁` has the same
assigned set and values at I's obs-parents agree, then
`frontierActiveInfoset S cfg₁ p = some I`.

This is weaker than `frontierActiveInfoset_eq_of_assigned_vals_eq` which
requires all assigned values to agree. Here we only need obs-parent values
of the specific infoset `I` to agree. -/
private theorem frontierActiveInfoset_transfer
    (cfg₁ cfg₂ : FrontierCfg S) (p : Player) (I : Infoset S p)
    (hact : frontierActiveInfoset S cfg₂ p = some I)
    (hassn : cfg₁.assigned = cfg₂.assigned)
    (hvals : ∀ x, x ∈ S.obsParents I.1.val →
      ∀ (h₁ : x ∈ cfg₁.assigned) (h₂ : x ∈ cfg₂.assigned),
        cfg₁.values ⟨x, h₁⟩ = cfg₂.values ⟨x, h₂⟩) :
    frontierActiveInfoset S cfg₁ p = some I := by
  have hfr := frontier_eq_of_assigned_eq S cfg₁ cfg₂ hassn
  -- I comes from the head of frontierInfosets at cfg₂
  -- I.2 = restrictCfg cfg₂ (obsParents I.1.val) at that node
  -- We show: the restrictCfg at cfg₁ for I.1.val gives I.2 too
  -- Then frontierInfosets at cfg₁ starts with I too (same frontier list)
  -- Step 1: I.1.val is in the frontier of cfg₂ (hence cfg₁)
  have hfr_I := activeInfoset_mem_frontier S cfg₂ p I hact
  have hfr_I₁ : I.1.val ∈ MAID.frontier S cfg₁ := by rw [hfr]; exact hfr_I
  -- Step 2: restrictCfg at cfg₁ for I.1.val's obs-parents equals I.2
  have hen₁ : enabled S cfg₁ I.1.val := by
    simpa [MAID.frontier] using hfr_I₁
  have hrc₁ : restrictCfg cfg₁ (S.obsParents I.1.val)
      (fun x hx => hen₁.2 (S.obs_sub I.1.val hx)) = I.2 := by
    ext ⟨x, hx⟩
    simp only [restrictCfg]
    have hen₂ : enabled S cfg₂ I.1.val := by
      simpa [MAID.frontier] using hfr_I
    have hmem₁ := hen₁.2 (S.obs_sub I.1.val hx)
    have hmem₂ := hen₂.2 (S.obs_sub I.1.val hx)
    have h1 := hvals x hx hmem₁ hmem₂
    have h2 := activeInfoset_obsParent_value S cfg₂ p I hact x hx hmem₂
    exact h1.trans h2
  -- Step 3: Show frontierActiveInfoset cfg₁ p = some I
  -- Use the generic filterMap_head? lemma
  unfold frontierActiveInfoset frontierInfosets at hact ⊢
  rw [show (MAID.frontier S cfg₁).toList =
      (MAID.frontier S cfg₂).toList from by rw [hfr]]
  -- Apply the generic lemma with the cfg₂ filterMap function
  -- Both filterMap functions agree on none/some (same frontier, same kind)
  -- and at the first some (I), they produce the same value (from hrc₁)
  refine filterMap_head?_eq_of_none_agree _ _ _ I hact ?_ ?_
  · -- hnone: f₂ a = none → f₁ a = none
    -- The none/some pattern depends only on frontier membership and
    -- node kind/player, which are the same for cfg₁ and cfg₂.
    intro nd _hmem hf₂_none
    -- Simplify: if nd ∉ frontier cfg₂, then nd ∉ frontier cfg₁
    -- If nd ∈ frontier, the match on kind and player check are the same
    -- Either way: f₂ nd = none implies f₁ nd = none
    by_cases hnd₂ : nd ∈ MAID.frontier S cfg₂
    · have hnd₁ : nd ∈ MAID.frontier S cfg₁ := by rw [hfr]; exact hnd₂
      -- After simplifying frontier membership, we need to show the match
      -- on kind gives the same none/some pattern
      -- The match depends only on S.kind nd, which is the same
      -- For non-p-decision nodes, both give none
      -- For p-decision nodes, both give some, contradicting hf₂_none
      simp only [hnd₂, dite_true] at hf₂_none
      simp only [hnd₁, dite_true]
      -- Both goal and hf₂_none have the same match on S.kind nd.
      -- The only case that produces `some` is decision q with q = p,
      -- but then hf₂_none = (some _ = none), contradiction.
      -- Revert so `split` handles both simultaneously.
      revert hf₂_none
      split
      · next q hk =>
        by_cases hq : q = p
        · simp [hq]
        · simp [hq]
      · intro; rfl
    · have hnd₁ : nd ∉ MAID.frontier S cfg₁ := by rw [hfr]; exact hnd₂
      simp [hnd₁]
  · -- hsome: f₂ a = some I → f₁ a = some I
    intro nd _hmem hf₂_some
    by_cases hnd₂ : nd ∈ MAID.frontier S cfg₂
    · have hnd₁ : nd ∈ MAID.frontier S cfg₁ := by rw [hfr]; exact hnd₂
      simp only [hnd₂, dite_true] at hf₂_some
      simp only [hnd₁, dite_true]
      -- Split the match on S.kind nd in both hf₂_some and goal
      revert hf₂_some; split
      · next q hk =>
        by_cases hq : q = p
        · subst hq; simp only [dite_true, Option.some.injEq]
          intro hIeq
          -- hIeq : ⟨⟨nd, _⟩, restrictCfg cfg₂ ...⟩ = I, so nd = I.1.val
          have hnd_I : nd = I.1.val := congrArg (·.1.1) hIeq
          rw [← hIeq]
          exact Sigma.ext rfl (heq_of_eq (funext fun ⟨x, hx⟩ => by
            simp only [restrictCfg]
            exact hvals x (hnd_I ▸ hx) _ _))
        · simp [hq]
      · simp
    · simp [hnd₂] at hf₂_some

/-- Weaker version: `frontierActiveInfoset` depends only on the assigned set
and values at obs-parents of frontier decision nodes. -/
private theorem frontierActiveInfoset_eq_of_obsParent_vals_eq
    (cfg₁ cfg₂ : FrontierCfg S) (p : Player)
    (hassn : cfg₁.assigned = cfg₂.assigned)
    (hvals : ∀ nd, nd ∈ MAID.frontier S cfg₁ →
      ∀ x, x ∈ S.obsParents nd →
        ∀ (h₁ : x ∈ cfg₁.assigned) (h₂ : x ∈ cfg₂.assigned),
        cfg₁.values ⟨x, h₁⟩ = cfg₂.values ⟨x, h₂⟩) :
    frontierActiveInfoset S cfg₁ p = frontierActiveInfoset S cfg₂ p := by
  suffices hInfosets : frontierInfosets S cfg₁ p = frontierInfosets S cfg₂ p by
    simp only [frontierActiveInfoset, hInfosets]
  unfold frontierInfosets
  have hfr := frontier_eq_of_assigned_eq S cfg₁ cfg₂ hassn
  rw [show (MAID.frontier S cfg₂).toList =
      (MAID.frontier S cfg₁).toList from by rw [hfr]]
  apply List.filterMap_congr
  intro nd hnd
  have hnd_fr : nd ∈ MAID.frontier S cfg₁ := by
    rwa [Finset.mem_toList] at hnd
  have hnd_fr₂ : nd ∈ MAID.frontier S cfg₂ := by rw [← hfr]; exact hnd_fr
  simp only [hnd_fr, hnd_fr₂, dite_true]
  split <;> try rfl
  next q hk =>
    by_cases hq : q = p
    · simp only [hq, dite_true]
      have hen₁ : enabled S cfg₁ nd := by simpa [MAID.frontier] using hnd_fr
      have hen₂ : enabled S cfg₂ nd := by simpa [MAID.frontier] using hnd_fr₂
      simp only [Option.some.injEq]
      refine Sigma.ext rfl (heq_of_eq (funext fun ⟨x, hx⟩ => ?_))
      simp only [restrictCfg]
      exact hvals nd hnd_fr x hx (hen₁.2 (S.obs_sub nd hx))
        (hen₂.2 (S.obs_sub nd hx))
    · simp [hq]

private theorem frontierCfg_values_cast (nd : Fin n)
    {c₁ c₂ : FrontierCfg S} (h : c₁ = c₂)
    (h₁ : nd ∈ c₁.assigned) (h₂ : nd ∈ c₂.assigned) :
    c₁.values ⟨nd, h₁⟩ = c₂.values ⟨nd, h₂⟩ := by subst h; rfl

/-- Value stability: for a feasible trace, values at `extendFrontier` are preserved
from the previous config for nodes already assigned. -/
private theorem value_stable_one_step
    (π : PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length)
    (nd : Fin n) (h₁ : nd ∈ ss[j].assigned) (h₂ : nd ∈ ss[j + 1].assigned) :
    ss[j + 1].values ⟨nd, h₂⟩ = ss[j].values ⟨nd, h₁⟩ := by
  have hstep := pureRun_step_nonzero
    (compiledPRObs S sem).pureStep (compiledPRObs S sem).machine.init
    k π ss (by rwa [runDistPure_eq_pureRun] at hss) j hj
  rw [ObsModelCore.pureStep_eq] at hstep
  have hlast := lastState_take_eq S sem ss j (by omega)
  -- hstep is at lastState. frontierStepPMF_preserves_old needs it at ss[j].
  -- Use assigned_eq_stepPR pattern: apply at lastState, rwa with hlast
  have := frontierStepPMF_preserves_old S sem
    ((compiledPRObs S sem).lastState (ss.take (j + 1))) _ ss[j + 1] hstep
    nd (hlast ▸ h₁) h₂
  exact this.trans (frontierCfg_values_cast S nd hlast _ h₁)

/-- Value stability: once a node is assigned, its value doesn't change. -/
private theorem value_stable_on_trace
    (π : PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j₁ j₂ : Nat) (hle : j₁ ≤ j₂) (hj₂ : j₂ < ss.length)
    (nd : Fin n)
    (h₁ : nd ∈ ss[j₁].assigned) (h₂ : nd ∈ ss[j₂].assigned) :
    ss[j₂].values ⟨nd, h₂⟩ = ss[j₁].values ⟨nd, h₁⟩ := by
  induction hle with
  | refl => rfl
  | step hle ih =>
    have h_mid : nd ∈ ss[‹Nat›].assigned :=
      assigned_mono_multi S sem π k ss hss j₁ _ hle (by omega) nd h₁
    rw [value_stable_one_step S sem π k ss hss _ (by omega) nd h_mid h₂,
        ih (by omega) h₁ h_mid]

/-- In a reachable config, `assigned` is upward-closed: if `nd ∈ assigned`, then
all parents of `nd` are also in `assigned`. -/
private theorem assigned_parents_closed
    (π : PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j : Nat) (hj : j < ss.length)
    (nd : Fin n) (hnd : nd ∈ ss[j].assigned)
    (x : Fin n) (hx : x ∈ S.parents nd) :
    x ∈ ss[j].assigned := by
  induction j with
  | zero =>
    have h0 := pureRun_getElem_zero S sem π k ss
      (by rwa [runDistPure_eq_pureRun] at hss) hj
    rw [h0] at hnd
    exact absurd hnd (Finset.notMem_empty _)
  | succ m ih =>
    rw [assigned_eq_on_trace_step S sem π k ss hss m hj] at hnd
    rcases Finset.mem_union.mp hnd with hnd_old | hnd_fr
    · -- nd was already assigned at step m
      have := ih (by omega) hnd_old
      exact (assigned_mono_on_trace S sem π k ss hss m hj
        (Finset.mem_union.mpr (Or.inl this)))
    · -- nd was in the frontier at step m → parents assigned at step m
      have hen : enabled S ss[m] nd := by simpa [MAID.frontier] using hnd_fr
      have := hen.2 hx
      exact (assigned_mono_on_trace S sem π k ss hss m hj
        (Finset.mem_union.mpr (Or.inl this)))

/-- On a feasible trace, if `a →+ b` (ancestor) and `b ∈ assigned`, then `a ∈ assigned`. -/
private theorem ancestor_assigned
    (π : PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j : Nat) (hj : j < ss.length)
    (a b : Fin n)
    (hanc : S.IsAncestor a b) (hb : b ∈ ss[j].assigned) :
    a ∈ ss[j].assigned := by
  induction hanc with
  | single h => exact assigned_parents_closed S sem π k ss hss j hj _ hb a h
  | tail htg hlast ih =>
    exact ih (assigned_parents_closed S sem π k ss hss j hj _ hb _ hlast)

/-- If `IsAncestor a b` and `b ∈ frontier S ss[j]` on a feasible trace,
then `a ∈ ss[j].assigned`. -/
private theorem ancestor_assigned_of_frontier
    (π : PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j : Nat) (hj : j < ss.length)
    (a b : Fin n)
    (hanc : S.IsAncestor a b) (hfr : b ∈ MAID.frontier S ss[j]) :
    a ∈ ss[j].assigned := by
  have hen : enabled S ss[j] b := by simpa [MAID.frontier] using hfr
  induction hanc with
  | single h => exact hen.2 h
  | tail htg hlast ih =>
    have hc := hen.2 hlast
    -- c ∈ assigned, and a →+ c. Use ancestor_assigned.
    exact ancestor_assigned S sem π k ss hss j hj a _ htg hc

/-- Under SAD, if both `π₀` and `Function.update π₀ p πᵢ` produce nonzero
on `ss`, then `πᵢ` agrees with `π₀ p` at every intermediate observation. -/
private theorem pureRun_update_nonzero_agree_compiledPR
    (p : Player) (π₀ : PureProfile (compiledPRObs S sem))
    (πᵢ : (compiledPRObs S sem).LocalStrategy p)
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : pureRun (compiledPRObs S sem).pureStep (compiledPRObs S sem).init k π₀ ss ≠ 0)
    (hupd : pureRun (compiledPRObs S sem).pureStep (compiledPRObs S sem).init k
      (Function.update π₀ p πᵢ) ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length) :
    πᵢ ((compiledPRObs S sem).projectStates p (ss.take (j + 1))) =
      π₀ p ((compiledPRObs S sem).projectStates p (ss.take (j + 1))) := by
  have hDet := stepActionDeterminism_compiledPR S sem
  have hlen := pureRun_length _ _ k π₀ ss hss
  induction k generalizing ss j with
  | zero => omega
  | succ m ih =>
    have hne : ss ≠ [] := by intro he; simp [he] at hlen
    obtain ⟨pre, t, hcat⟩ := List.eq_nil_or_concat ss |>.resolve_left hne
    rw [List.concat_eq_append] at hcat; subst hcat
    have hpre₀ := left_ne_zero_of_mul (pureRun_succ_append .. ▸ hss)
    have hpreU := left_ne_zero_of_mul (pureRun_succ_append .. ▸ hupd)
    have hlenP : pre.length = m + 1 := by simp at hlen; omega
    by_cases hjp : j + 1 < pre.length
    · -- j is in the prefix — use IH
      have htake_eq : (pre ++ [t]).take (j + 1) = pre.take (j + 1) :=
        List.take_append_of_le_length (by omega)
      rw [htake_eq]
      exact ih pre hpre₀ hpreU j hjp hlenP
    · -- j is the last index of pre
      have hjval : j + 1 = pre.length := by simp at hj; omega
      have htake_eq : (pre ++ [t]).take (j + 1) = pre := by
        rw [hjval, List.take_append_of_le_length (le_refl _), List.take_length]
      rw [htake_eq]
      have hstep := (pureRun_succ_nonzero_iff hDet m hss
        (Function.update π₀ p πᵢ)).mp hupd
      have hagree := hstep.2 p
      simp only [Function.update_self] at hagree
      exact hagree

/-- Under SAD, if `πᵢ` agrees with `π₀ p` at every intermediate observation,
then `Function.update π₀ p πᵢ` has the same `pureRun` probability as `π₀`. -/
private theorem pureRun_update_eq_of_obs_agree_compiledPR
    (p : Player) (π₀ : PureProfile (compiledPRObs S sem))
    (πᵢ : (compiledPRObs S sem).LocalStrategy p)
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : pureRun (compiledPRObs S sem).pureStep (compiledPRObs S sem).init k π₀ ss ≠ 0)
    (h : ∀ j (_ : j + 1 < ss.length),
      πᵢ ((compiledPRObs S sem).projectStates p (ss.take (j + 1))) =
        π₀ p ((compiledPRObs S sem).projectStates p (ss.take (j + 1)))) :
    pureRun (compiledPRObs S sem).pureStep (compiledPRObs S sem).init k
      (Function.update π₀ p πᵢ) ss =
    pureRun (compiledPRObs S sem).pureStep (compiledPRObs S sem).init k π₀ ss := by
  have hDet := stepActionDeterminism_compiledPR S sem
  induction k generalizing ss with
  | zero => rfl
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨pre, t, hcat⟩
    · exact absurd (pureRun_succ_nil _ _ m _) hss
    · rw [List.concat_eq_append] at hcat; subst hcat
      simp only [pureRun_succ_append] at hss ⊢
      have hpre₀ := left_ne_zero_of_mul hss
      have hlen : pre.length = m + 1 := pureRun_length _ _ m _ pre hpre₀
      have h' : ∀ j (hj : j + 1 < pre.length),
          πᵢ ((compiledPRObs S sem).projectStates p (pre.take (j + 1))) =
            π₀ p ((compiledPRObs S sem).projectStates p (pre.take (j + 1))) := by
        intro j hj
        have hjlt : j + 1 < (pre ++ [t]).length := by simp; omega
        have htake_eq : (pre ++ [t]).take (j + 1) = pre.take (j + 1) :=
          List.take_append_of_le_length (by omega)
        rw [← htake_eq]; exact h j hjlt
      have hpre_eq := ih pre hpre₀ h'
      have hstep_agree : πᵢ ((compiledPRObs S sem).projectStates p pre) =
          π₀ p ((compiledPRObs S sem).projectStates p pre) := by
        have hjlt : (pre.length - 1) + 1 < (pre ++ [t]).length := by simp; omega
        have htake_eq : (pre ++ [t]).take (pre.length - 1 + 1) = pre := by
          rw [show pre.length - 1 + 1 = pre.length from by omega,
            List.take_append_of_le_length (le_refl _), List.take_length]
        rw [← htake_eq]; exact h (pre.length - 1) hjlt
      -- Step equality: the forced action for update π₀ p πᵢ at pre = π₀ at pre
      -- because πᵢ agrees with π₀ p at projectStates p pre
      have ht₀ := right_ne_zero_of_mul hss
      have hstep_eq : (compiledPRObs S sem).pureStep (Function.update π₀ p πᵢ) pre t ≠ 0 := by
        rw [(pureStep_nonzero_iff_forall_player hDet ht₀ (Function.update π₀ p πᵢ))]
        intro q; by_cases hqp : q = p
        · subst hqp; simp [Function.update_self, hstep_agree]
        · simp [Function.update_of_ne hqp]
      have := pureStep_eq_of_nonzero_same hDet hstep_eq ht₀
      rw [hpre_eq, this]

/-- Transport through a dependent function: `h ▸ f a = f b` when `h : a = b`. -/
private theorem cast_dep_apply' {α : Type} {P : α → Type}
    (f : ∀ x, P x) {a b : α} (h : a = b) :
    h ▸ f a = f b := by cases h; rfl

/-- Heterogeneous version of composing a hidden inner transport with a visible
outer transport. This avoids matching on proof terms inside `▸`. -/
private theorem cast_dep_apply_trans_heq {α : Type} {P : α → Type}
    (f : ∀ x, P x) {a b c : α} {h₁ : a = b} (h₂ : b = c) :
    h₂ ▸ (h₁ ▸ f a) ≍ f c := by
  rw [eqRec_heq_iff_heq]
  exact (eqRec_heq _ (f a)).trans
    (eqRec_heq_iff_heq.mp (heq_of_eq (cast_dep_apply' f (h₁.trans h₂))))

/-- On a feasible trace, the value assigned to a decision node at step `j+1`
equals the profile's action at the corresponding infoset. -/
private theorem decision_value_eq_profile_action
    (π : PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length)
    (p : Player) (I : Infoset S p)
    (hact : frontierActiveInfoset S (ss[j]'(by omega)) p = some I)
    (hmem : I.1.val ∈ (ss[j + 1]'(by omega)).assigned) :
    (ss[j + 1]'(by omega)).values ⟨I.1.val, hmem⟩ = π p (some I) := by
  -- Step 1: extract the per-step nonzero condition
  have hstep := pureRun_step_nonzero
    (compiledPRObs S sem).pureStep (compiledPRObs S sem).machine.init
    k π ss (by rwa [runDistPure_eq_pureRun] at hss) j hj
  rw [ObsModelCore.pureStep_eq] at hstep
  have hlast := lastState_take_eq S sem ss j (by omega)
  -- hstep : frontierStepPMF_PR S sem (lastState (ss.take(j+1))) acts ss[j+1] ≠ 0
  -- where acts i = currentObs_projectStates i (ss.take(j+1)) ▸ π i (projectStates i ...)
  -- Step 2: rewrite lastState to ss[j]
  set cfg := (compiledPRObs S sem).lastState (ss.take (j + 1)) with hcfg_def
  -- Step 3: extract vals from the pushforward support
  -- frontierStepPMF_PR is frontierStepPMF with rawActs
  obtain ⟨vals, hext, hnd_ne⟩ := frontierStepPMF_support_vals S sem cfg _ ss[j + 1] hstep
  -- Step 4: show I.1.val is in the frontier at cfg = ss[j]
  have hFr : I.1.val ∈ MAID.frontier S cfg := by
    rw [hlast]; exact activeInfoset_mem_frontier S ss[j] p I hact
  -- Step 5: ss[j+1].values = vals at I.1.val
  have hvals_eq : (ss[j + 1]'(by omega)).values ⟨I.1.val, hmem⟩ = vals ⟨I.1.val, hFr⟩ := by
    have : ∀ (c : FrontierCfg S) (hc : I.1.val ∈ c.assigned),
        c = extendFrontier S cfg vals → c.values ⟨I.1.val, hc⟩ = vals ⟨I.1.val, hFr⟩ := by
      intro c hc heq; subst heq
      exact extendFrontier_sets_frontier S cfg vals I.1.val hFr hc
    exact this _ hmem hext.symm
  rw [hvals_eq]
  -- Step 6: vals at I.1.val = hp ▸ a p (from nodeDistrib_rawActs_eq)
  set a := fun i => (compiledPRObs S sem).currentObs_projectStates i (ss.take (j + 1)) ▸
    π i ((compiledPRObs S sem).projectStates i (ss.take (j + 1))) with ha_def
  have hp : frontierActiveInfoset S cfg p = some I := by rw [hlast]; exact hact
  have hval_eq := nodeDistrib_rawActs_eq S sem cfg p I hp hFr a
    (vals ⟨I.1.val, hFr⟩) (hnd_ne ⟨I.1.val, hFr⟩)
  rw [hval_eq]
  -- Step 7: hp ▸ a p = π p (some I) using cast_dep_apply
  -- a p = currentObs_projectStates p ss' ▸ π p (projectStates p ss')
  -- The final HEq proof avoids matching on the hidden proof term inside the
  -- inner transport, which is brittle across Lean versions.
  change (show CompiledMAIDAct S p (some I) from hp ▸ a p) = π p (some I)
  have ha_p : a p =
      ((compiledPRObs S sem).currentObs_projectStates p (ss.take (j + 1))) ▸
        π p ((compiledPRObs S sem).projectStates p (ss.take (j + 1))) := by
    simpa using congrFun ha_def p
  rw [ha_p]
  apply eq_of_heq
  exact cast_dep_apply_trans_heq (π p) hp

/-- Transfer of intermediate observation agreement between two feasible traces
with the same final observation, under PerfectRecall.

Under PerfectRecall with the identity info state, if `πᵢ` agrees with `π₀ p`
at every intermediate observation of `ss₁`, then `πᵢ` agrees with `π₀' p`
at every intermediate observation of `ss₂`, given that both traces have the
same final observation for player `p`.

This relies on the MAID PerfectRecall structure: intermediate nontrivial
observations (infosets) are ancestors of the final infoset and their forced
values are recorded in the final infoset's obs-parent values. -/
private theorem obs_agree_transfer
    (hPR : S.PerfectRecall) (p : Player)
    (π₀ π₀' : PureProfile (compiledPRObs S sem))
    (n₁ n₂ : Nat) (ss₁ ss₂ : List (FrontierCfg S))
    (hobs : (compiledPRObs S sem).projectStates p ss₁ =
      (compiledPRObs S sem).projectStates p ss₂)
    (h₁ : pureRun (compiledPRObs S sem).pureStep (compiledPRObs S sem).init n₁ π₀ ss₁ ≠ 0)
    (h₂ : pureRun (compiledPRObs S sem).pureStep (compiledPRObs S sem).init n₂ π₀' ss₂ ≠ 0)
    (hns : ¬ Subsingleton (CompiledMAIDAct S p
      ((compiledPRObs S sem).projectStates p ss₁)))
    (πᵢ : (compiledPRObs S sem).LocalStrategy p)
    (hagree₁ : ∀ j (_hj : j + 1 < ss₁.length),
      πᵢ ((compiledPRObs S sem).projectStates p (ss₁.take (j + 1))) =
        π₀ p ((compiledPRObs S sem).projectStates p (ss₁.take (j + 1))))
    (j : Nat) (hj : j + 1 < ss₂.length) :
    πᵢ ((compiledPRObs S sem).projectStates p (ss₂.take (j + 1))) =
      π₀' p ((compiledPRObs S sem).projectStates p (ss₂.take (j + 1))) := by
  -- Rewrite projectStates using identity info state
  have hlen₂ := pureRun_length _ _ n₂ π₀' ss₂ h₂
  rw [projectStates_identity_last S sem ss₂ p j (by omega)]
  match hobs_j : frontierActiveInfoset S (ss₂[j]'(by omega)) p with
  | none =>
    -- Player inactive at this step: action type is PUnit, agreement is trivial
    exact PUnit.ext _ _
  | some I_k =>
    -- Player active at infoset I_k. Need: πᵢ(some I_k) = π₀' p (some I_k)
    -- Step 1: Extract I_final from the final observation
    have hlen₁ := pureRun_length _ _ n₁ π₀ ss₁ h₁
    -- The final observations match (from hobs)
    -- projectStates p ss₁ = projectStates p ss₂
    -- With identity info state, this = frontierActiveInfoset S (lastState ss) p
    -- For full traces, lastState ss = ss[ss.length - 1]
    -- Use projectStates_identity_last with take (n-1+1) = take n = ss
    have hfinal₁ : (compiledPRObs S sem).projectStates p ss₁ =
        frontierActiveInfoset S ss₁[ss₁.length - 1] p := by
      have := projectStates_identity_last S sem ss₁ p (ss₁.length - 1) (by omega)
      rwa [show ss₁.length - 1 + 1 = ss₁.length from by omega, List.take_length] at this
    have hfinal₂ : (compiledPRObs S sem).projectStates p ss₂ =
        frontierActiveInfoset S ss₂[ss₂.length - 1] p := by
      have := projectStates_identity_last S sem ss₂ p (ss₂.length - 1) (by omega)
      rwa [show ss₂.length - 1 + 1 = ss₂.length from by omega, List.take_length] at this
    -- Since hns says the final obs is nontrivial, it must be `some I_final`
    rw [hfinal₁] at hns
    have hfinal_obs₁ : ∃ I_final, frontierActiveInfoset S ss₁[ss₁.length - 1] p = some I_final := by
      match h : frontierActiveInfoset S ss₁[ss₁.length - 1] p with
      | some I => exact ⟨I, rfl⟩
      | none => rw [h] at hns; exact absurd (inferInstanceAs (Subsingleton PUnit)) hns
    obtain ⟨I_final, hI_final₁⟩ := hfinal_obs₁
    -- Both traces have the same final infoset
    rw [hfinal₁, hfinal₂] at hobs
    have hI_final₂ : frontierActiveInfoset S ss₂[ss₂.length - 1] p = some I_final := by
      rw [← hobs, hI_final₁]
    -- Step 2: I_k.1.val is in the frontier at step j of ss₂
    have hfr_k := activeInfoset_mem_frontier S ss₂[j] p I_k hobs_j
    -- I_final.1.val is in the frontier at the last step
    have hfr_final := activeInfoset_mem_frontier S ss₂[ss₂.length - 1] p I_final hI_final₂
    -- If I_k = I_final, the final obs is the same and we can use hagree₁ directly
    -- If I_k ≠ I_final, by PerfectRecall they are comparable
    -- I_k gets assigned after step j, so I_k.1.val ∈ ss₂[j+1].assigned
    have hk_assigned_j1 : I_k.1.val ∈ ss₂[j + 1].assigned := by
      have := assigned_mono_on_trace S sem π₀' n₂ ss₂
        (by rwa [runDistPure_eq_pureRun]) j (by omega)
      exact this (Finset.mem_union.mpr (Or.inr hfr_k))
    -- I_final is NOT assigned at the last step (it's in the frontier)
    have hfinal_not_assigned := frontier_not_assigned S ss₂[ss₂.length - 1] I_final.1.val hfr_final
    -- I_k is NOT I_final: I_k gets assigned at j+1, but I_final is in the frontier
    -- at the last step (hence not assigned). Contradiction if they're the same node.
    have hne_node : I_k.1.val ≠ I_final.1.val := by
      intro heq
      have hk_at_last : I_k.1.val ∈ ss₂[ss₂.length - 1].assigned :=
        assigned_mono_multi S sem π₀' n₂ ss₂
          (by rwa [runDistPure_eq_pureRun]) (j + 1) (ss₂.length - 1)
          (by omega) (by omega) I_k.1.val hk_assigned_j1
      rw [heq] at hk_at_last
      exact hfinal_not_assigned hk_at_last
    -- By PerfectRecall temporal ordering, I_k and I_final are comparable
    have hcomp := hPR.1 p I_k.1.val I_final.1.val I_k.1.2 I_final.1.2 hne_node
    -- I_k is ancestor of I_final (if I_final were ancestor, it'd be assigned, contradiction)
    have hk_anc : S.IsAncestor I_k.1.val I_final.1.val := by
      rcases hcomp with hanc | hanc
      · exact hanc
      · exfalso
        have hf_at_j : I_final.1.val ∈ ss₂[j].assigned :=
          ancestor_assigned_of_frontier S sem π₀' n₂ ss₂
            (by rwa [runDistPure_eq_pureRun]) j (by omega)
            I_final.1.val I_k.1.val hanc hfr_k
        exact hfinal_not_assigned
          (assigned_mono_multi S sem π₀' n₂ ss₂
            (by rwa [runDistPure_eq_pureRun]) j (ss₂.length - 1)
            (by omega) (by omega) I_final.1.val hf_at_j)
    -- PerfectRecall gives obs-parent containment
    have ⟨hk_in_obs, hobs_sub⟩ := hPR.2 p I_k.1.val I_final.1.val I_k.1.2 I_final.1.2 hk_anc
    -- I_final is in the frontier at the last step of ss₁ too
    have hfr_final₁ := activeInfoset_mem_frontier S ss₁[ss₁.length - 1] p I_final hI_final₁
    -- I_k is an obs-parent of I_final, obs-parents ⊆ parents, parents ⊆ assigned (frontier)
    have hk_assigned_last₁ : I_k.1.val ∈ ss₁[ss₁.length - 1].assigned := by
      have hen : enabled S (ss₁[ss₁.length - 1]) I_final.1.val := by
        simpa [MAID.frontier] using hfr_final₁
      exact hen.2 (S.obs_sub I_final.1.val hk_in_obs)
    -- Prove j + 1 < ss₁.length by contradiction
    -- If not, then n₁ ≤ j. At step n₁ of both traces, assigned sets match.
    -- I_k is assigned at step n₁ of ss₁ (= last step). By assigned_eq_on_traces,
    -- I_k is assigned at step n₁ of ss₂. By monotonicity, at step j of ss₂.
    -- But I_k is in the frontier at step j of ss₂, contradiction.
    have hj₁' : j + 1 < ss₁.length := by
      by_contra hle
      push Not at hle
      -- ss₁.length = n₁ + 1, so n₁ + 1 ≤ j + 1, i.e., n₁ ≤ j
      have hn₁_le_j : n₁ ≤ j := by omega
      -- At step n₁ of both traces, assigned sets match
      have hassn_n₁ : (ss₁[n₁]'(by omega)).assigned = (ss₂[n₁]'(by omega)).assigned :=
        assigned_eq_on_traces S sem π₀ π₀' n₁ n₂ ss₁ ss₂
          (by rwa [runDistPure_eq_pureRun]) (by rwa [runDistPure_eq_pureRun])
          n₁ (by omega) (by omega)
      -- ss₁[n₁] is the last state of ss₁
      -- I_k is assigned at step n₁ of ss₂
      have hk_at_n₁ : I_k.1.val ∈ (ss₂[n₁]'(by omega)).assigned := by
        have : (ss₁[n₁]'(by omega)) = ss₁[ss₁.length - 1] := by
          congr 1; omega
        rw [← hassn_n₁, this]; exact hk_assigned_last₁
      -- By monotonicity, I_k is assigned at step j of ss₂
      have hk_at_j : I_k.1.val ∈ ss₂[j].assigned :=
        assigned_mono_multi S sem π₀' n₂ ss₂
          (by rwa [runDistPure_eq_pureRun]) n₁ j
          (by omega) (by omega) I_k.1.val hk_at_n₁
      -- But I_k is in the frontier at step j, hence not assigned
      exact (frontier_not_assigned S ss₂[j] I_k.1.val hfr_k) hk_at_j
    have hj₁ : j < ss₁.length := by omega
    -- Assigned sets match at step j across traces
    have hassn_j : (ss₁[j]'hj₁).assigned = ss₂[j].assigned :=
      assigned_eq_on_traces S sem π₀ π₀' n₁ n₂ ss₁ ss₂
        (by rwa [runDistPure_eq_pureRun]) (by rwa [runDistPure_eq_pureRun])
        j hj₁ (by omega)
    -- I_k appears at step j of ss₁ too
    -- The frontier at ss₁[j] = frontier at ss₂[j] (same assigned sets)
    -- I_k.1.val is the first p-decision node in the frontier (from hobs_j)
    -- We show the restrictCfg at I_k's obs-parents agrees in ss₁[j] and ss₂[j]
    -- by value stability through the last step and I_final
    have hobs_j₁ : frontierActiveInfoset S (ss₁[j]'hj₁) p = some I_k := by
      -- Show obs-parent values at I_k agree across traces
      have hvals_agree_Ik : ∀ x (hx : x ∈ S.obsParents I_k.1.val),
          ∀ (h₁ : x ∈ (ss₁[j]'hj₁).assigned) (h₂ : x ∈ ss₂[j].assigned),
          (ss₁[j]'hj₁).values ⟨x, h₁⟩ = ss₂[j].values ⟨x, h₂⟩ := by
        intro x hx_obs h₁ h₂
        have hx_obs_final := hobs_sub hx_obs
        -- ss₁[j] → ss₁[last₁] by value stability
        have h₁_last : x ∈ (ss₁[ss₁.length - 1]).assigned := by
          have hen : enabled S (ss₁[ss₁.length - 1]) I_final.1.val := by
            simpa [MAID.frontier] using hfr_final₁
          exact hen.2 (S.obs_sub I_final.1.val hx_obs_final)
        have hstable₁ := value_stable_on_trace S sem π₀ n₁ ss₁
          (by rwa [runDistPure_eq_pureRun]) j (ss₁.length - 1)
          (by omega) (by omega) x h₁ h₁_last
        -- ss₁[last₁].values(x) = I_final.2(x)
        have hval_final₁ := activeInfoset_obsParent_value S
          (ss₁[ss₁.length - 1]) p I_final hI_final₁ x hx_obs_final h₁_last
        -- ss₂[j] → ss₂[last₂] by value stability
        have h₂_last : x ∈ (ss₂[ss₂.length - 1]).assigned := by
          have hen : enabled S (ss₂[ss₂.length - 1]) I_final.1.val := by
            simpa [MAID.frontier] using hfr_final
          exact hen.2 (S.obs_sub I_final.1.val hx_obs_final)
        have hstable₂ := value_stable_on_trace S sem π₀' n₂ ss₂
          (by rwa [runDistPure_eq_pureRun]) j (ss₂.length - 1)
          (by omega) (by omega) x h₂ h₂_last
        -- ss₂[last₂].values(x) = I_final.2(x)
        have hval_final₂ := activeInfoset_obsParent_value S
          (ss₂[ss₂.length - 1]) p I_final hI_final₂ x hx_obs_final h₂_last
        -- Chain: ss₁[j] = ss₁[last₁] = I_final.2 = ss₂[last₂] = ss₂[j]
        exact (hstable₁.symm.trans hval_final₁).trans (hval_final₂.symm.trans hstable₂)
      exact frontierActiveInfoset_transfer S (ss₁[j]'hj₁) ss₂[j] p I_k
        hobs_j hassn_j hvals_agree_Ik
    -- Use hagree₁
    have hagree_k := hagree₁ j hj₁'
    rw [projectStates_identity_last S sem ss₁ p j hj₁, hobs_j₁] at hagree_k
    -- Show π₀ p (some I_k) = π₀' p (some I_k)
    -- Show π₀ p (some I_k) = π₀' p (some I_k) via assigned values
    have hk_assigned_j1_1 : I_k.1.val ∈ (ss₁[j + 1]'(by omega)).assigned := by
      have hfr_k₁ := activeInfoset_mem_frontier S (ss₁[j]'hj₁) p I_k hobs_j₁
      exact assigned_mono_on_trace S sem π₀ n₁ ss₁
        (by rwa [runDistPure_eq_pureRun]) j hj₁'
        (Finset.mem_union.mpr (Or.inr hfr_k₁))
    have hv₁ := decision_value_eq_profile_action S sem π₀ n₁ ss₁
      (by rwa [runDistPure_eq_pureRun]) j hj₁' p I_k hobs_j₁ hk_assigned_j1_1
    have hv₂ := decision_value_eq_profile_action S sem π₀' n₂ ss₂
      (by rwa [runDistPure_eq_pureRun]) j hj p I_k hobs_j hk_assigned_j1
    -- Value at I_k.1.val: ss₁[j+1] → ss₁[last₁] → I_final.2 → ss₂[last₂] → ss₂[j+1]
    have hk_assigned_last₂ : I_k.1.val ∈ (ss₂[ss₂.length - 1]).assigned :=
      assigned_mono_multi S sem π₀' n₂ ss₂
        (by rwa [runDistPure_eq_pureRun]) (j + 1) (ss₂.length - 1)
        (by omega) (by omega) I_k.1.val hk_assigned_j1
    have hstable₁ := value_stable_on_trace S sem π₀ n₁ ss₁
      (by rwa [runDistPure_eq_pureRun]) (j + 1) (ss₁.length - 1)
      (by omega) (by omega) I_k.1.val hk_assigned_j1_1 hk_assigned_last₁
    have hfinal₁_k := activeInfoset_obsParent_value S
      (ss₁[ss₁.length - 1]) p I_final hI_final₁ I_k.1.val hk_in_obs hk_assigned_last₁
    have hstable₂ := value_stable_on_trace S sem π₀' n₂ ss₂
      (by rwa [runDistPure_eq_pureRun]) (j + 1) (ss₂.length - 1)
      (by omega) (by omega) I_k.1.val hk_assigned_j1 hk_assigned_last₂
    have hfinal₂_k := activeInfoset_obsParent_value S
      (ss₂[ss₂.length - 1]) p I_final hI_final₂ I_k.1.val hk_in_obs hk_assigned_last₂
    -- Chain: π₀(I_k) = ss₁[j+1] = ss₁[last] = I_final.2 = ss₂[last] = ss₂[j+1] = π₀'(I_k)
    rw [hagree_k, hv₁.symm,
      hstable₁.symm.trans (hfinal₁_k.trans (hfinal₂_k.symm.trans hstable₂)), hv₂]

private theorem obsLocalFeasibility_compiledPR
    (hPR : S.PerfectRecall) (p : Player) :
    ObsLocalFeasibility (compiledPRObs S sem) p := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ hns πᵢ
  constructor
  · intro hup₁
    have hagree₁ := fun j hj =>
      pureRun_update_nonzero_agree_compiledPR S sem p π₀ πᵢ n₁ ss₁ h₁ hup₁ j hj
    rw [pureRun_update_eq_of_obs_agree_compiledPR S sem p π₀' πᵢ n₂ ss₂ h₂
      (fun j hj => obs_agree_transfer S sem hPR p π₀ π₀' n₁ n₂ ss₁ ss₂
        hobs h₁ h₂ hns πᵢ hagree₁ j hj)]
    exact h₂
  · intro hup₂
    have hagree₂ := fun j hj =>
      pureRun_update_nonzero_agree_compiledPR S sem p π₀' πᵢ n₂ ss₂ h₂ hup₂ j hj
    rw [pureRun_update_eq_of_obs_agree_compiledPR S sem p π₀ πᵢ n₁ ss₁ h₁
      (fun j hj => obs_agree_transfer S sem hPR p π₀' π₀ n₂ n₁ ss₂ ss₁
        hobs.symm h₂ h₁ (hobs ▸ hns) πᵢ hagree₂ j hj)]
    exact h₁

/-- Under perfect recall, `ActionPosteriorLocal` holds for every player
in the PR-compiled MAID. -/
theorem actionPosteriorLocal_compiledPR
    (hPR : S.PerfectRecall) (p : Player) :
    ObsModelCore.ActionPosteriorLocal (compiledPRObs S sem) p :=
  actionPosteriorLocal_of_obsLocalFeasibility
    (stepMassInvariant_compiledPR S sem) p
    (obsLocalFeasibility_compiledPR S sem hPR p)

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
        change (β p none : PMF PUnit) PUnit.unit =
          (PMF.pure PUnit.unit : PMF PUnit) PUnit.unit
        have := PMF.tsum_coe (show PMF PUnit from β p none)
        simpa [PMF.pure_apply] using this
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
