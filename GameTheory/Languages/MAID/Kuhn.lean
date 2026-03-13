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
      rw [← hnd_val]
      exact hnd_frontier
    · simp only [hq, ↓reduceDIte] at hnd_val
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

/-- On a reachable trace, assigned sets grow: frontier nodes at `j` are assigned at `j+1`. -/
private theorem assigned_mono_on_trace
    (π : ObsModelCore.PureProfile (compiledPRObs S sem))
    (k : Nat) (ss : List (FrontierCfg S))
    (hss : (compiledPRObs S sem).runDistPure k π ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length) :
    ss[j].assigned ∪ frontier S ss[j] ⊆ ss[j + 1].assigned := by
  -- On a runDistPure trace, ss[j+1] is in the support of pureStep at ss.take(j+1)
  -- pureStep calls the machine's step, which is frontierStepPMF_PR
  -- frontierStepPMF_PR calls frontierStepPMF = pushforward (pmfPi ...) (extendFrontier ...)
  -- So ss[j+1] = extendFrontier S ss[j] vals, giving assigned' = assigned ∪ frontier
  sorry

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

end GameTheory.Languages.MAID
