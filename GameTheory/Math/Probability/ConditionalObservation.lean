/-
# Conditioning through observation channels

An auxiliary observation whose law depends on the state only through an
existing observation does not change the posterior of the state. The same
calculation persists through a hidden-state transition when the new
observation determines the old one. Conversely, conditioning an expanded state
and then retracting it recovers the source posterior whenever the expansion's
observation law depends only on the source observation. Conditioning commutes
with keeping a readout, can be moved before a transition that determines the
observation, and is unchanged by a coarser earlier observation.

Every posterior here is the total `fiberPosterior`; hypotheses of positive
mass appear only where a fiber must actually be met.
-/

import GameTheory.Math.Probability.Conditioning

noncomputable section

namespace GameTheory.Math.Probability

variable {State Observation Noise : Type*}

/-- The second marginal of an independent pair law is its second factor. -/
theorem bindPairLaw_const_map_snd {α β : Type*} (first : PMF α) (second : PMF β) :
    (bindPairLaw first fun _ => second).map Prod.snd = second := by
  rw [bindPairLaw_map_snd, PMF.bind_const]

/-- Observing one independent coordinate leaves the other law unchanged,
including at an impossible observation. -/
theorem fiberPosterior_snd_bindPairLaw_const {α β : Type*} (first : PMF α) (second : PMF β)
    (observed : α) :
    (fiberPosterior (bindPairLaw first fun _ => second) Prod.fst observed).map Prod.snd =
      second := by
  by_cases present : observed ∈ ((bindPairLaw first fun _ => second).map Prod.fst).support
  · ext right
    rw [fiberPosterior_map_snd_apply _ _ present, bindPairLaw_apply, bindPairLaw_map_fst]
    rw [bindPairLaw_map_fst] at present
    rw [mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel ((PMF.mem_support_iff _ _).mp present)
      (PMF.apply_ne_top _ _), one_mul]
  · rw [fiberPosterior_of_not_mem_support _ _ present, bindPairLaw_map_snd, PMF.bind_const]

/-- An auxiliary observation drawn from a channel of the existing observation
leaves the posterior of the state unchanged. -/
theorem conditional_observation_kernel (prior : PMF State)
    (observe : State → Observation) (noise : Observation → PMF Noise)
    (observed : Observation) (extra : Noise)
    (present : observed ∈ (prior.map observe).support)
    (possible : extra ∈ (noise observed).support) :
    let joint := prior.bind fun state =>
      (noise (observe state)).map fun signal => (state, signal)
    (fiberPosterior joint (fun pair => (observe pair.1, pair.2)) (observed, extra)).map
      Prod.fst = fiberPosterior prior observe observed := by
  classical
  dsimp only
  let joint := prior.bind fun state =>
    (noise (observe state)).map fun signal => (state, signal)
  let information := fun pair : State × Noise => (observe pair.1, pair.2)
  obtain ⟨witness, supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp present
  have oldMeets : ∃ state ∈ {state | observe state = observed}, state ∈ prior.support :=
    ⟨witness, equal, supported⟩
  have meets : ∃ pair ∈ {pair | information pair = (observed, extra)}, pair ∈ joint.support := by
    refine ⟨(witness, extra), ?_, ?_⟩
    · exact Prod.ext equal rfl
    · simp only [joint, PMF.support_bind, Set.mem_iUnion]
      refine ⟨witness, supported, ?_⟩
      rw [PMF.support_map]
      exact ⟨extra, by simpa only [equal] using possible, rfl⟩
  have mapped : joint.map information = bindPairLaw (prior.map observe) noise := by
    simp only [joint, information, bindPairLaw, PMF.map_bind, PMF.map_comp, PMF.bind_map,
      Function.comp_def]
  have jointAt (state : State) (signal : Noise) :
      joint (state, signal) = prior state * noise (observe state) signal :=
    bindPairLaw_apply prior (fun state => noise (observe state)) state signal
  have mass : joint.toOuterMeasure {pair | information pair = (observed, extra)} =
      (prior.map observe) observed * noise observed extra := by
    rw [show {pair | information pair = (observed, extra)} =
        information ⁻¹' {(observed, extra)} from rfl,
      ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton, mapped,
      bindPairLaw_apply]
  have oldMass : prior.toOuterMeasure {state | observe state = observed} =
      (prior.map observe) observed := by
    rw [show {state | observe state = observed} = observe ⁻¹' {observed} from rfl,
      ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
  have noisePositive : noise observed extra ≠ 0 := (PMF.mem_support_iff _ _).mp possible
  have conditional : fiberPosterior joint information (observed, extra) =
      (fiberPosterior prior observe observed).map (fun state => (state, extra)) := by
    rw [fiberPosterior_eq_filter _ _ meets, fiberPosterior_eq_filter _ _ oldMeets]
    ext ⟨state, signal⟩
    rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, mass]
    by_cases signalEq : signal = extra
    · subst signal
      rw [pmf_map_apply_of_injective _ (fun _ _ same => (Prod.mk.inj same).1) state,
        PMF.filter_apply, ← PMF.toOuterMeasure_apply, oldMass]
      by_cases same : observe state = observed
      · have member : (state, extra) ∈ {pair | information pair = (observed, extra)} := by
          simp [information, same]
        rw [Set.indicator_of_mem member,
          Set.indicator_of_mem (show state ∈ {state | observe state = observed} from same),
          jointAt, same, ENNReal.mul_inv (Or.inr (PMF.apply_ne_top _ _))
            (Or.inr noisePositive), mul_comm (((prior.map observe) observed)⁻¹), ← mul_assoc,
          mul_assoc (prior state), ENNReal.mul_inv_cancel noisePositive (PMF.apply_ne_top _ _),
          mul_one]
      · have outside : (state, extra) ∉ {pair | information pair = (observed, extra)} := by
          simp [information, same]
        rw [Set.indicator_of_notMem outside, Set.indicator_of_notMem
          (show state ∉ {state | observe state = observed} from same), zero_mul, zero_mul]
    · have outside : (state, signal) ∉ {pair | information pair = (observed, extra)} := by
        simp [information, signalEq]
      rw [Set.indicator_of_notMem outside, zero_mul]
      symm
      apply (PMF.apply_eq_zero_iff _ _).mpr
      intro member
      obtain ⟨old, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact signalEq (congrArg Prod.snd same).symm
  change (fiberPosterior joint information (observed, extra)).map Prod.fst = _
  rw [conditional, PMF.map_comp]
  exact PMF.map_id _

/-- If the auxiliary input itself determines the old observation on its
supported fiber, conditioning on that input alone gives the source posterior. -/
theorem conditional_observation_kernel_recovered (prior : PMF State)
    (observe : State → Observation) (noise : Observation → PMF Noise)
    (observed : Observation) (extra : Noise)
    (present : ∃ state ∈ prior.support,
      observe state = observed ∧ extra ∈ (noise observed).support)
    (recovers : ∀ state ∈ prior.support, extra ∈ (noise (observe state)).support →
      observe state = observed) :
    let joint := prior.bind fun state =>
      (noise (observe state)).map fun signal => (state, signal)
    (fiberPosterior joint Prod.snd extra).map Prod.fst =
      fiberPosterior prior observe observed := by
  obtain ⟨witness, supported, matched, possible⟩ := present
  have oldPresent : observed ∈ (prior.map observe).support := by
    rw [PMF.support_map]
    exact ⟨witness, supported, matched⟩
  have ordinary := conditional_observation_kernel prior observe noise observed extra
    oldPresent possible
  dsimp only at ordinary ⊢
  have conditioning := fiberPosterior_eq_of_support_fiber
    (prior.bind fun state => (noise (observe state)).map fun signal => (state, signal))
    (fun pair => (observe pair.1, pair.2)) Prod.snd (observed, extra) extra (by
      intro pair member
      rw [PMF.support_bind] at member
      obtain ⟨state, stateSupport, member⟩ := Set.mem_iUnion₂.mp member
      rw [PMF.support_map] at member
      obtain ⟨signal, signalSupport, rfl⟩ := member
      exact ⟨fun equal => (Prod.mk.inj equal).2, fun equal =>
        Prod.ext (recovers state stateSupport (by rw [← equal]; exact signalSupport)) equal⟩)
  rw [conditioning] at ordinary
  exact ordinary

/-- The channel need only agree on supported states of each original
information fiber; a global factorization is constructed from those fibers. -/
theorem conditional_kernel_of_fiber (prior : PMF State)
    (observe : State → Observation) (kernel : State → PMF Noise)
    (same : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      observe left = observe right → kernel left = kernel right)
    (observed : Observation) (extra : Noise)
    (present : ∃ state ∈ prior.support,
      observe state = observed ∧ extra ∈ (kernel state).support) :
    let joint := prior.bind fun state =>
      (kernel state).map fun signal => (state, signal)
    (fiberPosterior joint (fun pair => (observe pair.1, pair.2)) (observed, extra)).map
      Prod.fst = fiberPosterior prior observe observed := by
  classical
  let noise := fun observed =>
    if existsState : ∃ state ∈ prior.support, observe state = observed then
      kernel existsState.choose
    else kernel prior.support_nonempty.choose
  have factors (state : State) (supported : state ∈ prior.support) :
      kernel state = noise (observe state) := by
    have existsState : ∃ other ∈ prior.support, observe other = observe state :=
      ⟨state, supported, rfl⟩
    simp only [noise, dite_eq_left existsState]
    exact same state supported existsState.choose existsState.choose_spec.1
      existsState.choose_spec.2.symm
  have joint : (prior.bind fun state => (kernel state).map fun signal => (state, signal)) =
      prior.bind fun state => (noise (observe state)).map fun signal => (state, signal) := by
    apply bind_congr_on_support _
    intro state supported
    rw [factors state supported]
  obtain ⟨state, supported, equal, possible⟩ := present
  have oldPresent : observed ∈ (prior.map observe).support := by
    rw [PMF.support_map]
    exact ⟨state, supported, equal⟩
  have noisePresent : extra ∈ (noise observed).support := by
    rw [← equal, ← factors state supported]
    exact possible
  dsimp only
  rw [joint]
  exact conditional_observation_kernel prior observe noise observed extra oldPresent noisePresent

/-- Auxiliary noise that is ancillary given an observation stays ancillary
through one hidden-state transition. The new observation must determine the
old observation, and the noise transition may depend on the hidden state and
action only through the new observation. Actions may depend on the whole
hidden state. -/
theorem exists_updated_observation_kernel
    {Action NextState NextObservation NextNoise : Type*}
    (prior : PMF State) (observe : State → Observation)
    (noise : Observation → PMF Noise) (choice : State → PMF Action)
    (advance : State → Action → NextState) (nextObserve : NextState → NextObservation)
    (channel : State → Action → Noise → PMF NextNoise)
    (reflects : ∀ left ∈ prior.support, ∀ leftAction ∈ (choice left).support,
      ∀ right ∈ prior.support, ∀ rightAction ∈ (choice right).support,
      nextObserve (advance left leftAction) = nextObserve (advance right rightAction) →
        observe left = observe right)
    (coupled : ∀ left ∈ prior.support, ∀ leftAction ∈ (choice left).support,
      ∀ right ∈ prior.support, ∀ rightAction ∈ (choice right).support,
      nextObserve (advance left leftAction) = nextObserve (advance right rightAction) →
      ∀ extra ∈ (noise (observe left)).support,
        channel left leftAction extra = channel right rightAction extra) :
    ∃ nextNoise : NextObservation → PMF NextNoise,
      (prior.bind fun state => (noise (observe state)).bind fun extra =>
        (choice state).bind fun action => (channel state action extra).map fun next =>
          (advance state action, next)) =
      (prior.bind fun state => (choice state).map (advance state)).bind fun state =>
        (nextNoise (nextObserve state)).map fun extra => (state, extra) := by
  classical
  let pairs := prior.bind fun state => (choice state).map fun action => (state, action)
  let observation := fun pair : State × Action => nextObserve (advance pair.1 pair.2)
  let branch := fun pair : State × Action =>
    (noise (observe pair.1)).bind (channel pair.1 pair.2)
  have supported (pair : State × Action) (member : pair ∈ pairs.support) :
      pair.1 ∈ prior.support ∧ pair.2 ∈ (choice pair.1).support := by
    rw [PMF.support_bind] at member
    obtain ⟨state, stateSupport, member⟩ := Set.mem_iUnion₂.mp member
    rw [PMF.support_map] at member
    obtain ⟨action, actionSupport, same⟩ := member
    cases same
    exact ⟨stateSupport, actionSupport⟩
  have same (left : State × Action) (leftSupport : left ∈ pairs.support)
      (right : State × Action) (rightSupport : right ∈ pairs.support)
      (equal : observation left = observation right) : branch left = branch right := by
    obtain ⟨leftPrior, leftAction⟩ := supported left leftSupport
    obtain ⟨rightPrior, rightAction⟩ := supported right rightSupport
    have priorView := reflects left.1 leftPrior left.2 leftAction right.1 rightPrior right.2
      rightAction equal
    change (noise (observe left.1)).bind _ = (noise (observe right.1)).bind _
    rw [← priorView]
    exact bind_congr_on_support _ fun extra member => coupled left.1 leftPrior left.2
      leftAction right.1 rightPrior right.2 rightAction equal extra member
  let nextNoise := fun view =>
    if present : ∃ pair ∈ pairs.support, observation pair = view then branch present.choose
    else branch pairs.support_nonempty.choose
  have factors (pair : State × Action) (member : pair ∈ pairs.support) :
      branch pair = nextNoise (observation pair) := by
    have present : ∃ other ∈ pairs.support, observation other = observation pair :=
      ⟨pair, member, rfl⟩
    simp only [nextNoise, dite_eq_left present]
    exact same pair member present.choose present.choose_spec.1 present.choose_spec.2.symm
  refine ⟨nextNoise, ?_⟩
  calc
    _ = pairs.bind (fun pair => (branch pair).map fun extra =>
        (advance pair.1 pair.2, extra)) := by
      simp only [pairs, branch, PMF.bind_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
      apply bind_congr_on_support _
      intro state _
      exact PMF.bind_comm _ _ _
    _ = pairs.bind (fun pair => (nextNoise (observation pair)).map fun extra =>
        (advance pair.1 pair.2, extra)) := by
      apply bind_congr_on_support _
      intro pair member
      rw [factors pair member]
    _ = _ := by simp only [pairs, observation, PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- Readout form of the ancillary-noise induction. A state may carry more
information than its source state and auxiliary readout; that remainder is
eliminated by coupling transitions on supported inputs. -/
theorem exists_updated_observation_kernel_of_readout
    {Native Action NextState NextObservation NextNoise : Type*}
    (law : PMF Native) (state : Native → State) (read : Native → Noise)
    (observe : State → Observation) (noise : Observation → PMF Noise)
    (factor : law.map (fun point => (state point, read point)) =
      (law.map state).bind fun source => (noise (observe source)).map fun extra => (source, extra))
    (choice : State → PMF Action) (advance : State → Action → NextState)
    (nextObserve : NextState → NextObservation) (step : Native → Action → PMF NextNoise)
    (reflects : ∀ left ∈ (law.map state).support, ∀ leftAction ∈ (choice left).support,
      ∀ right ∈ (law.map state).support, ∀ rightAction ∈ (choice right).support,
      nextObserve (advance left leftAction) = nextObserve (advance right rightAction) →
        observe left = observe right)
    (coupled : ∀ left ∈ law.support, ∀ leftAction ∈ (choice (state left)).support,
      ∀ right ∈ law.support, ∀ rightAction ∈ (choice (state right)).support,
      nextObserve (advance (state left) leftAction) =
        nextObserve (advance (state right) rightAction) →
      read left = read right → step left leftAction = step right rightAction) :
    ∃ nextNoise : NextObservation → PMF NextNoise,
      (law.bind fun point => (choice (state point)).bind fun action =>
        (step point action).map fun extra => (advance (state point) action, extra)) =
      ((law.map state).bind fun source => (choice source).map (advance source)).bind fun source =>
        (nextNoise (nextObserve source)).map fun extra => (source, extra) := by
  classical
  let joint := (law.map state).bind fun source =>
    (noise (observe source)).map fun extra => (source, extra)
  let representative := fun source extra =>
    if present : ∃ point ∈ law.support, (state point, read point) = (source, extra) then
      present.choose else law.support_nonempty.choose
  have realizes (source : State) (sourceSupport : source ∈ (law.map state).support)
      (extra : Noise) (extraSupport : extra ∈ (noise (observe source)).support) :
      representative source extra ∈ law.support ∧
      state (representative source extra) = source ∧
      read (representative source extra) = extra := by
    have jointSupport : (source, extra) ∈ joint.support := by
      rw [show joint = _ from rfl, PMF.support_bind]
      apply Set.mem_iUnion₂.mpr
      refine ⟨source, sourceSupport, ?_⟩
      rw [PMF.support_map]
      exact ⟨extra, extraSupport, rfl⟩
    change (source, extra) ∈ ((law.map state).bind fun source =>
      (noise (observe source)).map fun extra => (source, extra)).support at jointSupport
    rw [← factor, PMF.support_map] at jointSupport
    obtain ⟨point, pointSupport, same⟩ := jointSupport
    have present : ∃ point ∈ law.support, (state point, read point) = (source, extra) :=
      ⟨point, pointSupport, same⟩
    simp only [representative, dite_eq_left present]
    exact ⟨present.choose_spec.1, (Prod.mk.inj present.choose_spec.2).1,
      (Prod.mk.inj present.choose_spec.2).2⟩
  let channel := fun source action extra => step (representative source extra) action
  have channels : ∀ left ∈ (law.map state).support,
      ∀ leftAction ∈ (choice left).support, ∀ right ∈ (law.map state).support,
      ∀ rightAction ∈ (choice right).support,
      nextObserve (advance left leftAction) = nextObserve (advance right rightAction) →
      ∀ extra ∈ (noise (observe left)).support,
        channel left leftAction extra = channel right rightAction extra := by
    intro left leftSupport leftAction leftChoice right rightSupport rightAction rightChoice
      same extra extraSupport
    obtain ⟨leftPresent, leftState, leftRead⟩ := realizes left leftSupport extra extraSupport
    have priorView := reflects left leftSupport leftAction leftChoice right rightSupport
      rightAction rightChoice same
    obtain ⟨rightPresent, rightState, rightRead⟩ := realizes right rightSupport extra
      (by rwa [← priorView])
    apply coupled _ leftPresent leftAction (by rwa [leftState]) _ rightPresent rightAction
      (by rwa [rightState])
    · simpa only [leftState, rightState] using same
    · exact leftRead.trans rightRead.symm
  obtain ⟨nextNoise, nextLaw⟩ := exists_updated_observation_kernel (law.map state) observe noise
    choice advance nextObserve channel reflects channels
  refine ⟨nextNoise, ?_⟩
  calc
    _ = joint.bind (fun pair => (choice pair.1).bind fun action =>
        (channel pair.1 action pair.2).map fun extra => (advance pair.1 action, extra)) := by
      apply bind_eq_of_map_eq law joint (fun point => (state point, read point)) id
        (factor.trans (PMF.map_id joint).symm)
      intro point pointSupport pair pairSupport equal
      rw [PMF.support_bind] at pairSupport
      obtain ⟨source, sourceSupport, member⟩ := Set.mem_iUnion₂.mp pairSupport
      rw [PMF.support_map] at member
      obtain ⟨extra, extraSupport, pairEq⟩ := member
      cases pairEq
      have sourceEq : state point = source := (Prod.mk.inj equal).1
      have extraEq : read point = extra := (Prod.mk.inj equal).2
      obtain ⟨present, represented, readEq⟩ := realizes source sourceSupport extra extraSupport
      rw [sourceEq]
      apply bind_congr_on_support _
      intro action chosen
      have steps := coupled point pointSupport action (by rwa [sourceEq])
        (representative source extra) present action (by rwa [represented])
          (by rw [sourceEq, represented]) (extraEq.trans readEq.symm)
      exact congrArg (fun selected => selected.map fun next => (advance source action, next))
        steps
    _ = _ := by
      simpa only [joint, PMF.bind_bind, PMF.bind_map, Function.comp_def, channel] using nextLaw

/-- Re-encoding the state preserves an observation-local auxiliary law when
its new observation recovers the old one. -/
theorem map_observation_factor {Source View Extra Next NextView : Type*}
    (law : PMF (Source × Extra)) (observe : Source → View)
    (noise : View → PMF Extra)
    (factor : law = (law.map Prod.fst).bind fun state =>
      (noise (observe state)).map fun extra => (state, extra))
    (embed : Source → Next) (nextObserve : Next → NextView) (recover : NextView → View)
    (recovers : ∀ state, recover (nextObserve (embed state)) = observe state) :
    let mapped := law.map (fun pair => (embed pair.1, pair.2))
    mapped = (mapped.map Prod.fst).bind fun state =>
      (noise (recover (nextObserve state))).map fun extra => (state, extra) := by
  dsimp only
  have transformed := congrArg
    (fun μ : PMF (Source × Extra) => μ.map (fun pair => (embed pair.1, pair.2))) factor
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at transformed
  rw [transformed]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
    PMF.bind_map, PMF.bind_bind, PMF.bind_const, recovers]

/-- Conditioning on an observation of a readout commutes with keeping that
readout, on every observation of positive mass. -/
theorem map_fiberPosterior_readout {A B Info : Type*} (law : PMF A)
    (read : A → B) (observe : B → Info) (observed : Info)
    (present : observed ∈ (law.map (observe ∘ read)).support) :
    (fiberPosterior law (observe ∘ read) observed).map read =
      fiberPosterior (law.map read) observe observed := by
  classical
  rw [PMF.support_map] at present
  obtain ⟨point, supported, equal⟩ := present
  have originalMeets : ∃ a ∈ {a | (observe ∘ read) a = observed}, a ∈ law.support :=
    ⟨point, equal, supported⟩
  have imageMeets : ∃ b ∈ {b | observe b = observed}, b ∈ (law.map read).support := by
    refine ⟨read point, equal, ?_⟩
    rw [PMF.support_map]
    exact ⟨point, supported, rfl⟩
  rw [fiberPosterior_eq_filter _ _ originalMeets, fiberPosterior_eq_filter _ _ imageMeets]
  have massMap (μ : PMF A) (b : B) : (μ.map read) b = μ.toOuterMeasure (read ⁻¹' {b}) := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have normalizer : (law.map read).toOuterMeasure {b | observe b = observed} =
      law.toOuterMeasure {a | (observe ∘ read) a = observed} := by
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  ext value
  rw [massMap, toOuterMeasure_filter_apply, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
    normalizer, div_eq_mul_inv]
  by_cases same : observe value = observed
  · have inside : value ∈ {b | observe b = observed} := same
    have fiber : read ⁻¹' {value} ∩ {a | (observe ∘ read) a = observed} = read ⁻¹' {value} := by
      ext point
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
        Function.comp_apply]
      exact ⟨And.left, fun equal => ⟨equal, by rw [equal]; exact same⟩⟩
    rw [Set.indicator_of_mem inside, massMap, fiber]
  · have outside : value ∉ {b | observe b = observed} := same
    have empty : read ⁻¹' {value} ∩ {a | (observe ∘ read) a = observed} = ∅ := by
      ext point
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_and, Function.comp_apply]
      intro projected matching
      exact same (by rw [← projected]; exact matching)
    rw [Set.indicator_of_notMem outside, empty, MeasureTheory.measure_empty, zero_mul]

/-- **Retraction.** Conditioning an expanded state and retracting it recovers
the source posterior whenever the expansion's observation law is constant on
each supported source information fiber. The expanded observation may add
random distinctions, and the source state need not be independent of the
expansion. -/
theorem conditional_retraction {Source Native SourceInfo NativeInfo : Type*}
    (prior : PMF Source)
    (kernel : Source → PMF Native) (retract : Native → Source)
    (sourceObserve : Source → SourceInfo) (nativeObserve : Native → NativeInfo)
    (project : NativeInfo → SourceInfo)
    (commutes : ∀ a, sourceObserve (retract a) = project (nativeObserve a))
    (restores : ∀ s ∈ prior.support, ∀ a ∈ (kernel s).support, retract a = s)
    (locality : ∀ s ∈ prior.support, ∀ t ∈ prior.support,
      sourceObserve s = sourceObserve t →
        (kernel s).map nativeObserve = (kernel t).map nativeObserve)
    (observed : NativeInfo) (present : observed ∈ ((prior.bind kernel).map nativeObserve).support) :
    ((fiberPosterior (prior.bind kernel) nativeObserve observed).map retract) =
      fiberPosterior prior sourceObserve (project observed) := by
  classical
  let expanded := prior.bind kernel
  let read := fun a => (retract a, nativeObserve a)
  let information := fun pair : Source × NativeInfo => (sourceObserve pair.1, pair.2)
  let joint := prior.bind fun s =>
    ((kernel s).map nativeObserve).map fun signal => (s, signal)
  have jointLaw : expanded.map read = joint := by
    rw [PMF.map_bind]
    apply bind_congr_on_support _
    intro s supported
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro a member
    exact Prod.ext (restores s supported a member) rfl
  rw [PMF.support_map] at present
  obtain ⟨a, aSupport, aView⟩ := present
  have sourceSupport := aSupport
  rw [PMF.support_bind] at sourceSupport
  obtain ⟨s, sSupport, member⟩ := Set.mem_iUnion₂.mp sourceSupport
  have sourceView : sourceObserve s = project observed := by
    rw [← restores s sSupport a member, commutes, aView]
  have noisePresent : ∃ s ∈ prior.support,
      sourceObserve s = project observed ∧
        observed ∈ ((kernel s).map nativeObserve).support := by
    refine ⟨s, sSupport, sourceView, ?_⟩
    rw [PMF.support_map]
    exact ⟨a, member, aView⟩
  have augmentedPresent : (project observed, observed) ∈
      (expanded.map (information ∘ read)).support := by
    rw [PMF.support_map]
    refine ⟨a, aSupport, ?_⟩
    exact Prod.ext ((commutes a).trans (congrArg project aView)) aView
  have conditional : fiberPosterior expanded (information ∘ read) (project observed, observed) =
      fiberPosterior expanded nativeObserve observed := by
    apply fiberPosterior_eq_of_support_fiber
    intro value _
    change (sourceObserve (retract value), nativeObserve value) =
      (project observed, observed) ↔ nativeObserve value = observed
    rw [commutes]
    exact ⟨fun equal => (Prod.mk.inj equal).2,
      fun equal => Prod.ext (congrArg project equal) equal⟩
  have projected := map_fiberPosterior_readout expanded read information
    (project observed, observed) augmentedPresent
  rw [conditional, jointLaw] at projected
  have final := conditional_kernel_of_fiber prior sourceObserve
    (fun s => (kernel s).map nativeObserve) locality (project observed) observed noisePresent
  change ((fiberPosterior joint information (project observed, observed)).map Prod.fst) = _
    at final
  rw [← projected, PMF.map_comp] at final
  exact final

/-- If a transition determines its new observation from the old state,
conditioning can be performed before that transition. The transition laws are
unchanged; only the prior is conditioned. -/
theorem fiberPosterior_bind_of_observation {Source Native Info : Type*} (prior : PMF Source)
    (kernel : Source → PMF Native) (before : Source → Info) (after : Native → Info)
    (determines : ∀ s ∈ prior.support, ∀ a ∈ (kernel s).support, after a = before s)
    (observed : Info) (present : observed ∈ (prior.map before).support) :
    fiberPosterior (prior.bind kernel) after observed =
      (fiberPosterior prior before observed).bind kernel := by
  classical
  have observations : (prior.bind kernel).map after = prior.map before := by
    rw [PMF.map_bind, ← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro s supported
    calc
      (kernel s).map after = (kernel s).map (fun _ => before s) := by
        apply map_congr_on_support _
        exact determines s supported
      _ = PMF.pure (before s) := PMF.map_const _ _
  have newPresent : observed ∈ ((prior.bind kernel).map after).support := by
    rwa [observations]
  have mass : (prior.bind kernel).toOuterMeasure {a | after a = observed} =
      prior.toOuterMeasure {s | before s = observed} := by
    rw [show {a | after a = observed} = after ⁻¹' {observed} from rfl,
      show {s | before s = observed} = before ⁻¹' {observed} from rfl,
      ← PMF.toOuterMeasure_map_apply, observations, PMF.toOuterMeasure_map_apply]
  rw [fiberPosterior_of_mem_support _ _ newPresent, fiberPosterior_of_mem_support _ _ present]
  ext value
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, mass, PMF.bind_apply]
  by_cases matched : after value = observed
  · rw [Set.indicator_of_mem (show value ∈ {a | after a = observed} from matched),
      PMF.bind_apply, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro s
    rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply]
    by_cases supported : s ∈ prior.support
    · by_cases possible : value ∈ (kernel s).support
      · have view : s ∈ {s | before s = observed} :=
          (determines s supported value possible).symm.trans matched
        rw [Set.indicator_of_mem view]
        ring
      · rw [(PMF.apply_eq_zero_iff _ _).mpr possible]
        simp
    · have zero := (PMF.apply_eq_zero_iff _ _).mpr supported
      simp [Set.indicator, zero]
  · rw [Set.indicator_of_notMem (show value ∉ {a | after a = observed} from matched), zero_mul]
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro s
    rw [PMF.filter_apply]
    by_cases view : s ∈ {s | before s = observed}
    · by_cases supported : s ∈ prior.support
      · have impossible : value ∉ (kernel s).support := fun possible =>
          matched ((determines s supported value possible).trans view)
        rw [(PMF.apply_eq_zero_iff _ _).mpr impossible, mul_zero]
      · rw [Set.indicator_of_mem view, (PMF.apply_eq_zero_iff _ _).mpr supported]
        simp
    · rw [Set.indicator_of_notMem view]
      simp

/-- Once a finer observation is made, an earlier observation determined by it
does not further change the posterior. -/
theorem fiberPosterior_after_projection {A Info Coarse : Type*} (law : PMF A)
    (observe : A → Info) (project : Info → Coarse) (coarse : Coarse) (observed : Info)
    (present : observed ∈ ((fiberPosterior law (project ∘ observe) coarse).map observe).support) :
    fiberPosterior (fiberPosterior law (project ∘ observe) coarse) observe observed =
      fiberPosterior law observe observed := by
  classical
  by_cases coarseMeets : ∃ a ∈ {a | (project ∘ observe) a = coarse}, a ∈ law.support
  · rw [fiberPosterior_eq_filter _ _ coarseMeets] at present ⊢
    obtain ⟨a, aSupported, aView⟩ := (PMF.mem_support_map_iff _ _ _).mp present
    have aOriginal := ((PMF.mem_support_filter_iff _).mp aSupported).2
    have aCoarse := ((PMF.mem_support_filter_iff _).mp aSupported).1
    have projected : project observed = coarse := by
      change project (observe a) = coarse at aCoarse
      rwa [aView] at aCoarse
    have fineMeets : ∃ a ∈ {a | observe a = observed}, a ∈ law.support :=
      ⟨a, aView, aOriginal⟩
    have nestedMeets : ∃ a ∈ {a | observe a = observed},
        a ∈ (law.filter {a | (project ∘ observe) a = coarse} coarseMeets).support :=
      ⟨a, aView, aSupported⟩
    rw [fiberPosterior_eq_filter _ _ nestedMeets, fiberPosterior_eq_filter _ _ fineMeets]
    exact filter_filter_of_subset law _ _ coarseMeets nestedMeets fun value member => by
      change project (observe value) = coarse
      rw [show observe value = observed from member, projected]
  · rw [fiberPosterior_eq_self _ _ coarseMeets]

end GameTheory.Math.Probability
