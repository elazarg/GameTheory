/-
# Local point masses of the canonical history runner

An exact history carries its own predecessor. At its trace depth, only that
predecessor can contribute to its terminal point mass in one more runner step.
-/

import GameTheory.Protocol.HistoryEvents

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

/-- If one randomized step reaches a strictly deeper history, its immediate
predecessor is the starting history. -/
theorem runRandomizedFor_one_support_prior
    (chooser : E.RandomizedChooser) (start target : E.History)
    (hsupport : target ∈ (E.runRandomizedFor chooser 1 start).support)
    (hdepth : start.trace.length < target.trace.length) :
    target.prior = start := by
  have hreach := E.runRandomizedFor_reachesWithin chooser 1 start target hsupport
  cases hreach with
  | refl => omega
  | step joint legal realized rest =>
      have heq : target = start.extend legal realized :=
        (E.reachesWithin_zero_iff).mp rest
      subst target
      rfl

/-- At an exact trace depth, the history runner's point mass factors through
the target's canonical predecessor. This is a law of the existing runner,
not a separately defined path evaluator. -/
theorem runRandomizedFor_apply_of_trace_succ
    (chooser : E.RandomizedChooser) (fuel : ℕ)
    (start target : E.History)
    (hdepth : target.trace.length = start.trace.length + fuel + 1) :
    E.runRandomizedFor chooser (fuel + 1) start target =
      E.runRandomizedFor chooser fuel start target.prior *
        E.runRandomizedFor chooser 1 target.prior target := by
  rw [E.runRandomizedFor_add chooser fuel 1 start, PMF.bind_apply]
  apply tsum_eq_single target.prior
  intro prior hne
  by_cases hfirst : E.runRandomizedFor chooser fuel start prior = 0
  · simp [hfirst]
  have hfirstSupport :
      prior ∈ (E.runRandomizedFor chooser fuel start).support :=
    (PMF.mem_support_iff _ _).mpr hfirst
  have hreach := E.runRandomizedFor_reachesWithin chooser fuel start prior
    hfirstSupport
  have hlength : prior.trace.length ≤ start.trace.length + fuel :=
    hreach.trace_length_le_add
  by_cases hsecond : E.runRandomizedFor chooser 1 prior target = 0
  · simp [hsecond]
  have hsecondSupport :
      target ∈ (E.runRandomizedFor chooser 1 prior).support :=
    (PMF.mem_support_iff _ _).mpr hsecond
  have hprior := E.runRandomizedFor_one_support_prior chooser prior target
    hsecondSupport (by omega)
  exact False.elim (hne hprior.symm)

/-- Once a target history has terminated, extra runner fuel leaves its point
mass at that history unchanged. Earlier terminal histories cannot reach it. -/
theorem runRandomizedFor_apply_terminal_add
    (chooser : E.RandomizedChooser) (firstFuel extra : ℕ)
    (start target : E.History)
    (hdepth : target.trace.length = start.trace.length + firstFuel)
    (hterminal : E.terminal target.state) :
    E.runRandomizedFor chooser (firstFuel + extra) start target =
      E.runRandomizedFor chooser firstFuel start target := by
  rw [E.runRandomizedFor_add, PMF.bind_apply]
  have hsingle :
      (∑' prior, E.runRandomizedFor chooser firstFuel start prior *
        E.runRandomizedFor chooser extra prior target) =
        E.runRandomizedFor chooser firstFuel start target *
          E.runRandomizedFor chooser extra target target := by
    apply tsum_eq_single target
    intro prior hne
    by_cases hfirst : E.runRandomizedFor chooser firstFuel start prior = 0
    · simp [hfirst]
    by_cases hsecond : E.runRandomizedFor chooser extra prior target = 0
    · simp [hsecond]
    have hfirstSupport : prior ∈ (E.runRandomizedFor chooser firstFuel start).support :=
      (PMF.mem_support_iff _ _).mpr hfirst
    have hsecondSupport : target ∈ (E.runRandomizedFor chooser extra prior).support :=
      (PMF.mem_support_iff _ _).mpr hsecond
    have hreach := E.runRandomizedFor_reachesWithin chooser extra prior target
      hsecondSupport
    have hshape := E.runRandomizedFor_terminal_or_length chooser firstFuel
      start prior hfirstSupport
    have heq : target = prior := by
      rcases hshape with hpriorTerminal | hlength
      · exact hreach.eq_of_terminal hpriorTerminal
      · exact hreach.eq_of_trace_length_eq (by
          have hle := hreach.trace_length_le
          omega)
    exact False.elim (hne heq.symm)
  rw [hsingle, E.runRandomizedFor_of_terminal chooser extra hterminal]
  simp

/-- A bounded run cannot have positive mass beyond its trace budget. -/
theorem runRandomizedFor_apply_eq_zero_of_length_gt
    (chooser : E.RandomizedChooser) (fuel : ℕ)
    (start target : E.History)
    (hgt : start.trace.length + fuel < target.trace.length) :
    E.runRandomizedFor chooser fuel start target = 0 := by
  by_contra hne
  have hsupport : target ∈ (E.runRandomizedFor chooser fuel start).support :=
    (PMF.mem_support_iff _ _).mpr hne
  have hreach := E.runRandomizedFor_reachesWithin chooser fuel start target hsupport
  exact (not_le_of_gt hgt) hreach.trace_length_le_add

/-- Before consuming all fuel, a nonterminal target has zero point mass. -/
theorem runRandomizedFor_apply_eq_zero_of_length_lt_of_not_terminal
    (chooser : E.RandomizedChooser) (fuel : ℕ)
    (start target : E.History)
    (hlt : target.trace.length < start.trace.length + fuel)
    (hnot : ¬ E.terminal target.state) :
    E.runRandomizedFor chooser fuel start target = 0 := by
  by_contra hne
  have hsupport : target ∈ (E.runRandomizedFor chooser fuel start).support :=
    (PMF.mem_support_iff _ _).mpr hne
  rcases E.runRandomizedFor_terminal_or_length chooser fuel start target hsupport with
    hterm | hlength
  · exact hnot hterm
  · omega

/-- A nonempty exact history extends its canonical predecessor by one
realized legal step. -/
theorem History.prior_reachesWithin_one (target : E.History)
    (hpositive : 0 < target.trace.length) :
    E.ReachesWithin 1 target.prior target := by
  rcases target with ⟨state, trace⟩
  cases trace with
  | start => simp [Trace.length] at hpositive
  | extend prior joint legal realized =>
      exact .step joint legal realized (.refl 0 _)

/-- Peeling a nonempty trace removes exactly one transition. -/
theorem History.prior_trace_length (target : E.History)
    (hpositive : 0 < target.trace.length) :
    target.prior.trace.length + 1 = target.trace.length := by
  rcases target with ⟨state, trace⟩
  cases trace with
  | start => simp [Trace.length] at hpositive
  | extend prior joint legal realized => rfl

/-- One-step history laws only inspect the chooser at the starting history. -/
theorem runRandomizedFor_one_congr_at_start
    (first second : E.RandomizedChooser) (start : E.History)
    (hagree : ∀ hterm : ¬ E.terminal start.state,
      first start hterm = second start hterm) :
    E.runRandomizedFor first 1 start =
      E.runRandomizedFor second 1 start := by
  by_cases hterm : E.terminal start.state
  · rw [E.runRandomizedFor_of_terminal first 1 hterm,
      E.runRandomizedFor_of_terminal second 1 hterm]
  · rw [E.runRandomizedFor_succ_of_not_terminal first 0 hterm,
      E.runRandomizedFor_succ_of_not_terminal second 0 hterm,
      hagree hterm]
    simp only [E.runRandomizedFor_zero]

/-- At an exact trace depth, a target's point mass depends only on chooser
answers at ancestors of that target. -/
theorem runRandomizedFor_apply_congr_of_ancestors
    (first second : E.RandomizedChooser) (fuel : ℕ)
    (start target : E.History)
    (hdepth : target.trace.length = start.trace.length + fuel)
    (hagree : ∀ (prior : E.History)
      (hterm : ¬ E.terminal prior.state),
      (∃ n, E.ReachesWithin n prior target) →
        first prior hterm = second prior hterm) :
    E.runRandomizedFor first fuel start target =
      E.runRandomizedFor second fuel start target := by
  induction fuel generalizing target with
  | zero =>
      simp only [E.runRandomizedFor_zero]
  | succ fuel ih =>
      have hpositive : 0 < target.trace.length := by omega
      have hpriorDepth :
          target.prior.trace.length = start.trace.length + fuel := by
        have hlength := target.prior_trace_length hpositive
        omega
      have hstep := target.prior_reachesWithin_one hpositive
      have hprefix : E.runRandomizedFor first fuel start target.prior =
          E.runRandomizedFor second fuel start target.prior := by
        apply ih target.prior hpriorDepth
        intro prior hterm hreach
        obtain ⟨n, hreach⟩ := hreach
        exact hagree prior hterm ⟨n + 1, hreach.trans hstep⟩
      have hlocal := E.runRandomizedFor_one_congr_at_start
        first second target.prior
        (fun hterm => hagree target.prior hterm ⟨1, hstep⟩)
      rw [E.runRandomizedFor_apply_of_trace_succ first fuel start target (by omega),
        E.runRandomizedFor_apply_of_trace_succ second fuel start target (by omega),
        hprefix, hlocal]

/-- From the initial history, a target point mass at any fuel only inspects
chooser answers along that target's ancestors. Terminal targets absorb extra
fuel; nonterminal targets at shorter depth have zero mass. -/
theorem runRandomizedFor_apply_congr_from_init
    (first second : E.RandomizedChooser) (fuel : ℕ) (target : E.History)
    (hagree : ∀ (prior : E.History)
      (hterm : ¬ E.terminal prior.state),
      (∃ n, E.ReachesWithin n prior target) →
        first prior hterm = second prior hterm) :
    E.runRandomizedFor first fuel E.initHistory target =
      E.runRandomizedFor second fuel E.initHistory target := by
  have hexact : E.runRandomizedFor first target.trace.length E.initHistory target =
      E.runRandomizedFor second target.trace.length E.initHistory target :=
    E.runRandomizedFor_apply_congr_of_ancestors first second
      target.trace.length E.initHistory target
      (by simp [ExecutionProtocol.initHistory, Trace.length]) hagree
  rcases lt_trichotomy fuel target.trace.length with hshort | heq | hlong
  · rw [E.runRandomizedFor_apply_eq_zero_of_length_gt first fuel E.initHistory
        target (by simpa [ExecutionProtocol.initHistory, Trace.length] using hshort),
      E.runRandomizedFor_apply_eq_zero_of_length_gt second fuel E.initHistory
        target (by simpa [ExecutionProtocol.initHistory, Trace.length] using hshort)]
  · rw [heq]
    exact hexact
  · by_cases hterminal : E.terminal target.state
    · obtain ⟨extra, hfuel⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hlong)
      rw [hfuel,
        E.runRandomizedFor_apply_terminal_add first target.trace.length extra
          E.initHistory target
          (by simp [ExecutionProtocol.initHistory, Trace.length]) hterminal,
        E.runRandomizedFor_apply_terminal_add second target.trace.length extra
          E.initHistory target
          (by simp [ExecutionProtocol.initHistory, Trace.length]) hterminal]
      exact hexact
    · rw [E.runRandomizedFor_apply_eq_zero_of_length_lt_of_not_terminal
          first fuel E.initHistory target
          (by simpa [ExecutionProtocol.initHistory, Trace.length] using hlong) hterminal,
        E.runRandomizedFor_apply_eq_zero_of_length_lt_of_not_terminal
          second fuel E.initHistory target
          (by simpa [ExecutionProtocol.initHistory, Trace.length] using hlong) hterminal]

end ExecutionProtocol

namespace InformationModel

variable (M : InformationModel E)

/-- The information coordinates queried along a complete trace, including its
endpoint. The endpoint is included to make ancestor transport uniform; an
exact-depth point mass only consults the preceding coordinates. -/
def queriedInfos (M : InformationModel E) (i : ι) :
    ∀ {state : E.State}, E.Trace state → List (M.InfoState i)
  | _, .start => [M.infoOf i .start]
  | _, .extend prior joint legal realized =>
      M.infoOf i (.extend prior joint legal realized) :: M.queriedInfos i prior

theorem infoOf_mem_queriedInfos (i : ι) (h : E.History) :
    M.infoOf i h.trace ∈ M.queriedInfos i h.trace := by
  cases h with
  | mk state trace =>
      cases trace <;> simp [queriedInfos]

theorem queriedInfos_mono_reachesWithin (i : ι)
    {fuel : ℕ} {start target : E.History}
    (hreach : E.ReachesWithin fuel start target) :
    ∀ {info}, info ∈ M.queriedInfos i start.trace →
      info ∈ M.queriedInfos i target.trace := by
  induction hreach with
  | refl => exact fun hmem => hmem
  | step joint legal realized rest ih =>
      intro info hmem
      apply ih
      exact List.mem_cons_of_mem _ hmem

/-- Equality on the finitely many coordinates of one target trace suffices for
the exact-depth pure-run point mass, regardless of policy behavior elsewhere. -/
theorem runFrom_apply_congr_of_queriedInfos
    (first second : (i : ι) → M.Policy i)
    (fuel : ℕ) (start target : E.History)
    (hdepth : target.trace.length = start.trace.length + fuel)
    (hagree : ∀ i info, info ∈ M.queriedInfos i target.trace →
      first i info = second i info) :
    M.runFrom first fuel start target = M.runFrom second fuel start target := by
  rw [runFrom, runFrom,
    ← E.runRandomizedFor_toRandomized (M.historyChooser first) fuel start,
    ← E.runRandomizedFor_toRandomized (M.historyChooser second) fuel start]
  apply E.runRandomizedFor_apply_congr_of_ancestors _ _ fuel start target hdepth
  intro prior hterm hreach
  apply congrArg PMF.pure
  apply Subtype.ext
  apply funext
  intro i
  have hinfo : M.infoOf i prior.trace ∈ M.queriedInfos i target.trace := by
    obtain ⟨n, hreach⟩ := hreach
    exact M.queriedInfos_mono_reachesWithin i hreach
      (M.infoOf_mem_queriedInfos i prior)
  exact congrArg Subtype.val (hagree i _ hinfo)

/-- The same finite target-trace coordinates determine the exact-depth
behavioral point mass. -/
theorem runBehavioralFrom_apply_congr_of_queriedInfos
    [Fintype ι]
    (first second : (i : ι) → M.BehavioralPolicy i)
    (fuel : ℕ) (start target : E.History)
    (hdepth : target.trace.length = start.trace.length + fuel)
    (hagree : ∀ i info, info ∈ M.queriedInfos i target.trace →
      first i info = second i info) :
    M.runBehavioralFrom first fuel start target =
      M.runBehavioralFrom second fuel start target := by
  unfold runBehavioralFrom
  apply E.runRandomizedFor_apply_congr_of_ancestors _ _ fuel start target hdepth
  intro prior hterm hreach
  apply M.behavioralJoint_congr
  intro i
  obtain ⟨n, hreach⟩ := hreach
  exact hagree i _ (M.queriedInfos_mono_reachesWithin i hreach
    (M.infoOf_mem_queriedInfos i prior))

/-- At any fuel from the initial history, finite target-trace agreement fixes
the target point mass of a pure policy profile. -/
theorem run_apply_congr_of_queriedInfos
    (first second : (i : ι) → M.Policy i)
    (fuel : ℕ) (target : E.History)
    (hagree : ∀ i info, info ∈ M.queriedInfos i target.trace →
      first i info = second i info) :
    M.run first fuel target = M.run second fuel target := by
  unfold run runFrom
  rw [← E.runRandomizedFor_toRandomized (M.historyChooser first) fuel E.initHistory,
    ← E.runRandomizedFor_toRandomized (M.historyChooser second) fuel E.initHistory]
  apply E.runRandomizedFor_apply_congr_from_init
  intro prior hterm hreach
  apply congrArg PMF.pure
  apply Subtype.ext
  apply funext
  intro i
  obtain ⟨n, hreach⟩ := hreach
  have hinfo := M.queriedInfos_mono_reachesWithin i hreach
    (M.infoOf_mem_queriedInfos i prior)
  exact congrArg Subtype.val (hagree i _ hinfo)

/-- The same finite target-trace agreement fixes a behavioral point mass at
any fuel from the initial history. -/
theorem runBehavioral_apply_congr_of_queriedInfos [Fintype ι]
    (first second : (i : ι) → M.BehavioralPolicy i)
    (fuel : ℕ) (target : E.History)
    (hagree : ∀ i info, info ∈ M.queriedInfos i target.trace →
      first i info = second i info) :
    M.runBehavioral first fuel target =
      M.runBehavioral second fuel target := by
  unfold runBehavioral runBehavioralFrom
  apply E.runRandomizedFor_apply_congr_from_init
  intro prior hterm hreach
  apply M.behavioralJoint_congr
  intro i
  obtain ⟨n, hreach⟩ := hreach
  exact hagree i _ (M.queriedInfos_mono_reachesWithin i hreach
    (M.infoOf_mem_queriedInfos i prior))

end InformationModel

end GameTheory.Protocol
